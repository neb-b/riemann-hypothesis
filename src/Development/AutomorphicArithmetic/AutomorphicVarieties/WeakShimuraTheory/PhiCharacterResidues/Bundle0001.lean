module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.GroupDeterminantExistsUniqueDescentOfInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantIdentities

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.AdjEqConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_mul (R : Type) [CommRing R] : (formJ R).transpose * formJ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem adj_eq_conj {R : Type} [CommRing R] (M : M4 R) :
    adj M = formJ R * (M.transpose * (formJ R).transpose) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

theorem UpperTheory.V.Ws.phiAdj :
    ∀ {R : Type} [CommRing R] (ν : R) (M N : M4 R), IsGSp ν M → M * N = 1 → (ν • N).charpoly = M.charpoly := by
  intro R _ ν M N hM hMN
  have h1 : adj M = ν • N := by
    have h2 : adj M * M * N = ν • N := by
      unfold IsGSp at hM
      rw [hM, smul_mul_assoc, one_mul]
    rw [mul_assoc, hMN, mul_one] at h2
    exact h2
  rw [← h1, adj_eq_conj, Matrix.charpoly_mul_comm, mul_assoc, formJ_mul, mul_one, Matrix.charpoly_transpose]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_smul_unit {R n : Type} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (c : R) (hc : IsUnit c) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  have hinj : ∀ p q : R[X], p.comp (C c * X) = q.comp (C c * X) → p = q := by
    intro p q h
    ext i
    have hi := congrArg (fun r => r.coeff i) h
    simp only [comp_C_mul_X_coeff] at hi
    exact (hc.pow i).mul_right_cancel hi
  have key : (Polynomial.eval₂RingHom C (C c * X)).mapMatrix (Matrix.charmatrix (c • M)) =
      C c • Matrix.charmatrix M := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.charmatrix_apply_eq, Matrix.smul_apply, C_mul, mul_sub]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, C_mul]
  have hL : (c • M).charpoly.comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    calc (c • M).charpoly.comp (C c * X)
        = Polynomial.eval₂RingHom C (C c * X) (Matrix.charmatrix (c • M)).det := rfl
      _ = (C c • Matrix.charmatrix M).det := by rw [RingHom.map_det, key]
      _ = C c ^ Fintype.card n * M.charpoly := by rw [Matrix.det_smul]; rfl
  have hR : (M.charpoly.scaleRoots c).comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    ext i
    rw [comp_C_mul_X_coeff, coeff_scaleRoots, ← C_pow, coeff_C_mul, Matrix.charpoly_natDegree_eq_dim]
    by_cases hi : i ≤ Fintype.card n
    · rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega)]
      simp
  apply hinj
  rw [hL, hR]

theorem UpperTheory.V.Ws.phiCpMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (X.cp (resLe T.F_le g)).Monic ∧ (X.cp (resLe T.F_le g)).natDegree = 4 ∧ (K.cpT X n g).Monic ∧ (K.cpT X n g).map (algebraMap X.B X.A) = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hinj : Function.Injective (algebraMap X.B X.A) := X.inj
  haveI : Nontrivial X.A := hinj.nontrivial
  have hmap := X.cp_map (resLe T.F_le g)
  have hmon : (X.cp (resLe T.F_le g)).Monic :=
    monic_of_injective hinj (by rw [hmap]; exact Matrix.charpoly_monic _)
  have hdeg : (X.cp (resLe T.F_le g)).natDegree = 4 := by
    rw [← natDegree_map_eq_of_injective hinj, hmap, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hmonT : (K.cpT X n g).Monic := by
    show ((X.cp (resLe T.F_le g)).scaleRoots _).leadingCoeff = 1
    rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
    exact hmon
  refine ⟨hmon, hdeg, hmonT, ?_⟩
  have hu : IsUnit (K.sc n g) := by
    simp only [UpperTheory.V.Ws.Link.sc]
    exact (Units.isUnit _).mul ((Units.isUnit _).pow n)
  show ((X.cp (resLe T.F_le g)).scaleRoots _).map (algebraMap X.B X.A) = _
  rw [map_scaleRoots _ _ _ (by rw [hmon.leadingCoeff, map_one]; exact one_ne_zero), hmap,
    UpperTheory.V.Ws.Link.rho_apply, charpoly_smul_unit _ _ (hu.map _), ← IsScalarTower.algebraMap_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem val_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
    ValuationSubring.mem_inv_pointwise_smul_iff]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero]

open scoped Pointwise in
private theorem conj_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v ∧ ∀ σ ∈ Ine (F := F) A, t⁻¹ * σ * t ∈ Ine (F := F) (t⁻¹ • A) := by
  refine ⟨fun x => ?_, fun σ hσ => ?_⟩
  · rw [val_lt, AlgEquiv.commutes]
    exact h x
  · obtain ⟨hd, hi⟩ := hσ
    refine ⟨?_, fun x hx => ?_⟩
    · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      rw [mul_smul, mul_smul, smul_inv_smul, hd]
    · rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_inv_pointwise_smul_iff,
        AlgEquiv.smul_def] at hx
      rw [val_lt, map_sub]
      have := hi (t x) ((ValuationSubring.valuation_le_one_iff A _).2 hx)
      simpa [AlgEquiv.mul_apply, mul_inv_apply] using this

theorem UpperTheory.V.Ws.phiKer :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), Function.Surjective V.pr ∧ Topology.IsQuotientMap V.pr ∧ ∀ U : Subgroup (G L Ω), IsClosed (U : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ U) → V.pr.ker ≤ U := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have hres : ∀ (g : G L Ω) (x : Ω), W.resP L Ω g x = g x := fun _ _ => rfl
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => by rw [← hres a x, ← hres b x, h]
  have hsurj : Function.Surjective V.pr := by
    rintro ⟨y, hy⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y
    obtain ⟨g, rfl⟩ := (V.hη g').1 hy
    exact ⟨g, rfl⟩
  have hcont : Continuous V.pr := V.pr_cont W.continuous_resP
  haveI : IsClosed ((NS Ω V.S' : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
  haveI : T2Space (GS Ω V.S') := by
    unfold GS
    infer_instance
  refine ⟨hsurj, (hcont.isClosedMap).isQuotientMap hcont hsurj, fun U hU hI g hg => ?_⟩
  open scoped Pointwise in
  have hsm : ∀ (g : G L Ω) (B : ValuationSubring Ω), W.resP L Ω g • B = g • B := by
    intro g B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
      AlgEquiv.smul_def, hres]
  have hM : IsClosed ((U.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hU.isCompact).image W.continuous_resP).isClosed
  have hle : NS Ω V.S' ≤ U.map (W.resP L Ω) := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hM
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    rw [Group.mem_conjugatesOfSet_iff] at hc
    obtain ⟨a, ha, hac⟩ := hc
    obtain ⟨d, rfl⟩ := isConj_iff.1 hac
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop] at ha
    obtain ⟨v, hv, A, hA, haA⟩ := ha
    have key := conj_place hA d⁻¹
    simp only [inv_inv] at key
    obtain ⟨hA', hconj⟩ := key
    have hb := hconj a haA
    obtain ⟨g0, hg0⟩ := s.unr _ v hA' hb
    refine ⟨g0, hI _ v hA' hv ?_, hg0⟩
    rw [← hg0] at hb
    obtain ⟨hd, hi⟩ := hb
    refine ⟨?_, fun x hx => ?_⟩
    · open scoped Pointwise in
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      open scoped Pointwise in
      rwa [← hsm]
    · have := hi x hx
      rwa [hres] at this
  have hgN : W.resP L Ω g ∈ NS Ω V.S' := by
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨u, hu, hug⟩ := hle hgN
  rw [← hinj hug]
  exact hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CoprimeOfResidue
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem coprime_of_residue {B : Type} [CommRing B] [IsLocalRing B] (p q : B[X]) (hp : p.Monic)
    (h : IsCoprime (p.map (residue B)) (q.map (residue B))) : IsCoprime p q := by
  rw [← isUnit_resultant_iff_isCoprime hp]
  have hp' : (p.map (residue B)).Monic := hp.map _
  have h1 := (isUnit_resultant_iff_isCoprime hp').2 h
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (f := residue B) (p := q))
  have h2 : residue B (p.resultant q) = (p.map (residue B)).resultant (q.map (residue B)) := by
    rw [← resultant_map_map, hj, resultant_add_right_deg _ _ _ _ _ le_rfl,
      ← hp.natDegree_map (residue B), hp'.coeff_natDegree, one_pow, one_mul]
  rw [← h2] at h1
  exact (isUnit_map_iff (residue B) _).1 h1

theorem UpperTheory.V.Ws.phiRigid :
    ∀ {B E k : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field k] (f : B →+* k), (∀ x, f x = 0 → x ∈ maximalIdeal B) → ∀ (M : E) (p : B[X]) (d m : ℕ), p.Monic → aeval M p = 0 → p.map f = (Polynomial.X - 1) ^ d → M ^ m = 1 → IsUnit (m : B) → M = 1 := by
  intro B E k _ _ _ _ _ f hf M p d m hp hM hpf hm hu
  have h1 : p.map (residue B) = (Polynomial.X - 1) ^ d := by
    have h0 : (p - (Polynomial.X - 1) ^ d).map f = 0 := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hpf]
    have h2 : (p - (Polynomial.X - 1) ^ d).map (residue B) = 0 := by
      ext i
      rw [coeff_map, coeff_zero, residue_eq_zero_iff]
      apply hf
      rw [← coeff_map, h0, coeff_zero]
    simpa [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero] using h2
  set S : B[X] := ∑ i ∈ Finset.range m, Polynomial.X ^ i with hS
  have hc : IsCoprime p S := by
    apply coprime_of_residue p S hp
    rw [h1]
    apply IsCoprime.pow_left
    have hirr : Irreducible (Polynomial.X - C (1 : ResidueField B)) := irreducible_X_sub_C 1
    rw [← C_1, hirr.coprime_iff_not_dvd, dvd_iff_isRoot]
    have h3 : ((m : ℕ) : ResidueField B) ≠ 0 := by
      have := (hu.map (residue B)).ne_zero
      rwa [map_natCast] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [hS, Polynomial.map_sum, eval_finsetSum] using h3
  obtain ⟨a, b, hab⟩ := hc
  have h4 : aeval M b * aeval M S = 1 := by
    have := congrArg (aeval M) hab
    simpa [hM] using this
  have h5 : aeval M S * (M - 1) = 0 := by
    have : aeval M S = ∑ i ∈ Finset.range m, M ^ i := by simp [hS]
    rw [this, geom_sum_mul, hm, sub_self]
  have h6 : M - 1 = 0 := by
    have := congrArg (aeval M b * ·) h5
    simpa only [← mul_assoc, h4, one_mul, mul_zero] using this
  exact sub_eq_zero.1 h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hr := IsTotallyReal.complexEmbedding_isReal (j.comp (algebraMap T.F Ω))
    have := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.1 hr) x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at this
    apply j.injective
    rw [hj]
    exact this
  have hstab : ∀ (τ : G (W.Lp T.L) Ω) (x : T.L), ∃ y : T.L, τ (x : Ω) = y := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.c.toRingEquiv) (fun x => hfixF x)
  refine ⟨cF, fun g => ?_⟩
  let σ : G (W.Lp T.L) Ω := s.c * W.resP T.L Ω g * s.c⁻¹
  have hσ : ∀ x : T.L, σ (x : Ω) = x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have h1 : g (y : Ω) = y := g.commutes y
    have h2 : s.c (y : Ω) = x := by
      rw [← hy]
      exact mul_inv_apply (σ := s.c) (x : Ω)
    show s.c (g (s.c⁻¹ (x : Ω))) = x
    rw [hy, h1, h2]
  let g' : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hσ x)
  refine ⟨g', ?_, ?_⟩
  · ext x
    rfl
  · ext x
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiDet
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [CommRing B] [CommRing A] [Group H] [Group G] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace G] (I : Ideal B) [IsHausdorff I B] (f : B →+* A), Function.Injective f → ∀ (π : H →* G), Function.Surjective π → Topology.IsQuotientMap π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → B[X]), (∀ g, (cp g).map f = (ρ g).charpoly) → (∀ j, AdicCont I fun g => (cp g).coeff j) → (∀ U : Subgroup H, IsClosed (U : Set H) → ρ.ker ≤ U → π.ker ≤ U) → ∃ D : W.GDet n B G, (D.comap π).map f = W.GDet.ofRep ρ ∧ (∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g) ∧ D.IsCont I :=
  _root_.UpperTheory.Reformulated.B.DeterminantIdentities.phiDet
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v : W.Vl l T.L, W.HasFlag ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) fun i => W.pushCh (algebraMap X.B X.A) (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v
  have hlow := X.pair.low (K.e v)
  have h1 : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := by
    have h0 := hlow.1
    simpa [UpperTheory.V.GradeZeroInterpolatingElement.IsGSp] using h0
  have h2 : X.P.n (K.e v) * adj (X.P.n (K.e v)) = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩, fun s => ?_⟩
  obtain ⟨s, hs⟩ := s
  have hs' : resLe T.F_le s ∈ (T.fr ∅).Gv (K.e v) := by
    show resLe T.F_le s ∈ Dec (F := T.F) (T.pl (K.e v))
    rw [← K.hA v]
    exact hs
  have hval : (((⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A) *
      ((K.rho X n).toHomUnits.comp (Dec (F := T.L) (K.s.A v)).subtype) ⟨s, hs⟩ *
      (⟨adj (X.P.n (K.e v)), X.P.n (K.e v), h1, h2⟩ : GL (Fin 4) X.A)⁻¹ : GL (Fin 4) X.A) :
        Matrix (Fin 4) (Fin 4) X.A) =
      (algebraMap c'.O X.A (K.sc n s)) • (adj (X.P.n (K.e v)) * X.P.r (resLe T.F_le s) * X.P.n (K.e v)) := by
    simp [UpperTheory.V.Ws.Link.rho_apply, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, X.pair.flag (K.e v) _ hs' i j hij, smul_zero]
  · rw [hval, Matrix.smul_apply]
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i ⟨s, hs⟩, map_mul, ← IsScalarTower.algebraMap_apply, X.ψ_map _ _ _ hs', smul_eq_mul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiMu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiMu :
    ∀ {l : ℕ} [Fact l.Prime] {H Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (f : H →* Γ), Continuous f → ∀ D : Subgroup Γ, (∀ g, f g ∈ D) → ∀ g ∈ W.muG l H, f g ∈ muOf l D := by
  intro l _ H Γ _ _ _ _ _ _ f hf D hD g hg
  refine ⟨hD g, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (QuotientGroup.mk' (commutator H).topologicalClosure g) ^ l ^ k = 1 := hg
  refine ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hk
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
  rw [← map_pow, ← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  have hle : (⊤ : Subgroup H).map f ≤ D := by
    rintro _ ⟨x, _, rfl⟩
    exact hD x
  have h3 : f '' (commutator H : Set H) ⊆ ((⁅D, D⁆ : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : f x ∈ (commutator H).map f := ⟨x, hx, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at hx'
    exact Subgroup.commutator_mono hle hle hx'
  exact closure_mono h3 (image_closure_subset_closure_image hf ⟨_, h1, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ K.V.S' → Ine (F := T.L) A ≤ (K.rho X n).ker := by
  intro Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg
  have hS : v ∉ K.s.S := by rw [← K.hV]; exact hv
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro hlt
    apply hS
    left
    apply (hA (l : 𝓞 (W.Lp T.L))).1
    simpa using hlt
  obtain ⟨hκ, hr⟩ := K.unr A v hA hS g hg
  have hβ : K.β g = 1 := K.β_t (K.t_unr A hl hg)
  have hmem : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' : p = l := by simpa using hp
      rw [hp']
      exact hl
    · exact hg
    · have he : resQ T.F (resLe T.F_le g) = resQ T.L g := by
        ext x
        rfl
      rw [he]
      exact hr
  rw [MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]
  have hsc : K.sc n g = 1 := by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]
  rw [hsc, map_one, one_smul]
  exact X.pair.kill _ hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.SpacePsiMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiPsiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∃ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ := by
  intro Ω _ _ _ l _ c D T c' h K X n
  have hmem : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)),
      resLe (Tower.F_le T) (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    show _ ∈ Dec (T.pl (K.e v))
    have hg : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := K.hA v ▸ g.2
    exact hg
  have hup : ∀ (M N : GradeZeroInterpolatingElement.M4 X.A), IsUp M → IsUp N → ∀ i, (M * N) i i = M i i * N i i := by
    intro M N hM hN i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hM i k hlt, zero_mul]
      · rw [hN k i hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hleft : ∀ w, adj (X.P.n w) * X.P.n w = 1 := by
    intro w
    have h1 := (X.pair.low w).1
    simpa [IsGSp] using h1
  have hright : ∀ w, X.P.n w * adj (X.P.n w) = 1 := fun w => mul_eq_one_comm.mp (hleft w)
  have hPmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.P.ψ w i (s * t) = X.P.ψ w i s * X.P.ψ w i t := by
    intro w i s hs t ht
    have key : adj (X.P.n w) * X.P.r (s * t) * X.P.n w
        = (adj (X.P.n w) * X.P.r s * X.P.n w) * (adj (X.P.n w) * X.P.r t * X.P.n w) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.P.n w) (adj (X.P.n w)), hright w, Matrix.one_mul]
    unfold PD.ψ
    rw [key]
    exact hup _ _ (X.pair.flag w s hs) (X.pair.flag w t ht) i
  have hψmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.ψ w i (s * t) = X.ψ w i s * X.ψ w i t := by
    intro w i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map w i _ (mul_mem hs ht), X.ψ_map w i s hs, X.ψ_map w i t ht]
    exact hPmul w i s hs t ht
  have hψone : ∀ w i, X.ψ w i 1 = 1 := by
    intro w i
    apply X.inj
    rw [map_one, X.ψ_map w i 1 (one_mem _)]
    unfold PD.ψ
    rw [map_one, Matrix.mul_one, hleft w, Matrix.one_apply_eq]
  have hψunit : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, IsUnit (X.ψ w i s) := by
    intro w i s hs
    by_contra hne
    have h0 : IsLocalRing.residue X.B (X.ψ w i s) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hne)
    have hr := X.ψ_red w i s hs
    have hu := ((((T.fr ∅).χ i s).isUnit.map (inc h)).map (IsLocalRing.residue c'.O))
    rw [← hr] at hu
    simp only [res, h0] at hu
    simp at hu
    exact hne hu
  have hsc : ∀ g g' : G T.L Ω, K.sc n (g * g') = K.sc n g * K.sc n g' := by
    intro g g'
    unfold Link.sc
    simp only [map_mul, Units.val_mul, mul_pow]
    ring
  have hsc1 : K.sc n 1 = 1 := by
    unfold Link.sc
    simp
  have hscu : ∀ g : G T.L Ω, IsUnit (K.sc n g) := by
    intro g
    exact (K.κ g).isUnit.mul ((K.β g).isUnit.pow n)
  refine ⟨fun v i => IsUnit.liftRight
    { toFun := fun g => algebraMap c'.O X.B (K.sc n (g : G T.L Ω)) *
        X.ψ (K.e v) i (resLe (Tower.F_le T) (g : G T.L Ω))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one, hsc1]
        rw [one_mul]
        exact hψone (K.e v) i
      map_mul' := by
        intro g g'
        simp only [Subgroup.coe_mul]
        rw [map_mul (resLe (Tower.F_le T)), hψmul _ _ _ (hmem v g) _ (hmem v g'), hsc, map_mul]
        ring }
    (fun g => ((hscu (g : G T.L Ω)).map (algebraMap c'.O X.B)).mul (hψunit _ _ _ (hmem v g))), ?_⟩
  intro v i g
  rfl
end

