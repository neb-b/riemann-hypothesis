module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.auChi :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (c : Coef l), W.pushCh (algebraMap c.O (PadicAlgCl l)) (chiO F Ω l c.O) = cycBar F Ω l ∧ Continuous (cycBar F Ω l) := by
  intro F Ω _ _ _ _ _ l _ c
  refine ⟨?_, ?_⟩
  · ext g
    simp only [W.pushCh, chiO, cycBar, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      MonoidHom.coe_coe, RingHom.coe_comp]
    exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) _
  · have h1 : Continuous (algebraMap ℚ_[l] (Qbar l)) := continuous_algebraMap ℚ_[l] (Qbar l)
    have h2 : Continuous (PadicInt.Coe.ringHom (p := l)) := continuous_subtype_val
    have h3 : Continuous ⇑((algebraMap ℚ_[l] (Qbar l)).comp (PadicInt.Coe.ringHom (p := l))) :=
      h1.comp h2
    exact (Continuous.units_map
      (((algebraMap ℚ_[l] (Qbar l)).comp (PadicInt.Coe.ringHom (p := l))) : ℤ_[l] →* Qbar l)
      h3).comp (continuous_cycZ F Ω l)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.auSign :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] (μ : G ℚ Ω →* C) (c c' : G ℚ Ω), Af.IsConjEl c → Af.IsConjEl c' → μ c = μ c' := by
  intro Ω _ _ _ C _ μ c c' hc hc'
  obtain ⟨j, hj⟩ := hc
  obtain ⟨j', hj'⟩ := hc'
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  let σ : Ω ≃ₐ[ℚ] Ω := AlgHom.restrictNormal' j'.toRatAlgHom Ω
  have hσ : ∀ x, j (σ x) = j' x := fun x => by
    have h := AlgHom.restrictNormal_commutes j'.toRatAlgHom Ω x
    simp only [RingHom.algebraMap_toAlgebra, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.toRatAlgHom_apply] at h
    exact h
  have key : σ * c' = c * σ := by
    ext x
    apply j.injective
    show j (σ (c' x)) = j (c (σ x))
    rw [hσ, hj', hj, hσ]
  have h2 := congrArg μ key
  rw [map_mul, map_mul, mul_comm (μ c) (μ σ)] at h2
  exact (mul_left_cancel h2).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.CharpolySmulScale
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_smul_scale {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  haveI : Infinite K := CharZero.infinite K
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_univ.mono ?_
  intro t _
  simp only [Set.mem_setOf_eq]
  have ht : t = c * (c⁻¹ * t) := by field_simp
  rw [ht, Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hs := Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c
  rw [Fintype.card_fin] at hs
  rw [← hs]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq, mul_sub]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, mul_sub]

private theorem chi_comap_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (g : H) : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  simp [W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single]
  rw [← MonoidAlgebra.mapDomainRingHom_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single,
    map_one]

private theorem chi_map_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let F : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have h := D.nat A[X] B[X] F (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
  have e : MonoidAlgebra.mapRingHom G (F : A[X] →+* B[X])
      (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1 := by
    simp only [map_sub, MonoidAlgebra.mapRingHom_single, map_one]
    change MonoidAlgebra.single 1 (Polynomial.map f X) - MonoidAlgebra.single g 1 = _
    rw [Polynomial.map_X]
  rw [e] at h
  simp only [W.GDet.chi, W.GDet.map, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  exact h

private theorem scale_point {A B K : Type} [CommRing A] [CommRing B] [Field K] [CharZero K] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* K) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) (hb : y (i b) ≠ 0) : (p.scaleRoots b).map (y.comp i) = (y (i b) • M.map y).charpoly := by
  haveI : Nontrivial A := y.domain_nontrivial
  have hlc : i p.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_map_of_injective hi, hp]
    exact (Matrix.charpoly_monic M).leadingCoeff
  rw [Polynomial.map_scaleRoots _ _ _ (by simp [hlc]), ← Polynomial.map_map, hp, ← Matrix.charpoly_map,
    RingHom.comp_apply, charpoly_smul_scale _ hb]

theorem UpperTheory.V.Ws.auRep :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → x.IsRep (Af.tw ((X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) (K.κ * K.β ^ n))) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx
  unfold W.UniversalOrdinaryDeterminantRing.Pt.IsRep
  rw [W.UniversalOrdinaryDeterminantRing.Pt.D.eq_1]
  apply CA.d_gext
  intro g i _ _
  rw [W.GDet.lam.eq_1, W.GDet.lam.eq_1, (AlgebraTools.Det.repApi _).2.1]
  erw [chi_comap_single, chi_map_single]
  congr 2
  have hxφ : (x : B.B →+* PadicAlgCl l) =
      ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B) := by
    ext b
    exact hx b
  have e : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B
      (↑(K.κ g) * ↑(K.β g) ^ n))) = algebraMap c'.O (PadicAlgCl l) (↑(K.κ g) * ↑(K.β g) ^ n) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact y.commutes _
  rw [hxφ, ← Polynomial.map_map]
  erw [hφ.1 g]
  rw [scale_point (algebraMap X.B X.A) X.inj (y : X.A →+* PadicAlgCl l) _ (X.P.r _) (X.cp_map _), e]
  · set_option maxRecDepth 4096 in
    congr 1
    simp [W.mat.eq_1, Af.tw_val, W.pushCh.eq_1, PD.map.eq_1]
    rfl
  · rw [e]
    have u := (Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n)).ne_zero
    simpa using u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem irr_of_stab {k Γ H : Type} [Field k] [Group Γ] [Group H] (r : Γ →* M4 k) (hr : Irr r)
    (ρ : H →* GL (Fin 4) k)
    (h : ∀ g, ∃ (s : H) (t : k), r g = t • (ρ s : Matrix (Fin 4) (Fin 4) k)) : Af.IsIrr ρ := by
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have key : ∀ M : Matrix (Fin 4) (Fin 4) k, ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M
    have hM : M ∈ Submodule.span k (Set.range r) := by
      have h1 : Submodule.span k (Set.range r) = ⊤ := hr
      rw [h1]; exact Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨s, t, hs⟩ := h g
      intro v hv
      rw [hs, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW s v hv)
    | zero => intro v _; rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact W.smul_mem _ (hx v hv)
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hi' : v i ≠ 0 := hi
  refine eq_top_iff.2 fun w _ => ?_
  have h2 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
  have h3 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0 : Matrix (Fin 4) (Fin 4) k).mulVec v = w := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_assoc, inv_mul_cancel₀ hi', mul_one]
  rwa [h3] at h2

theorem UpperTheory.V.Ws.auIrr :
    ∀ {k Γ Γ' : Type} [Field k] [Group Γ] [Group Γ'] (r : Γ →* M4 k) (r' : Γ' →* M4 k), Irr r → (∀ g, ∃ g', r' g' = r g) → Af.IsIrr r'.toHomUnits ∧ ∀ χ : Γ' →* kˣ, Af.IsIrr (Af.tw r'.toHomUnits χ) := by
  intro k Γ Γ' _ _ _ r r' hr h
  refine ⟨irr_of_stab r hr _ fun g => ?_, fun χ => irr_of_stab r hr _ fun g => ?_⟩
  · obtain ⟨s, hs⟩ := h g
    exact ⟨s, 1, by rw [one_smul, ← hs]; rfl⟩
  · obtain ⟨s, hs⟩ := h g
    refine ⟨s, ((χ s : k))⁻¹, ?_⟩
    rw [Af.tw_val, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul, ← hs]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PairJAdj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.pairJ (k : Type) [Field k] : M4 k := !![0,0,0,1; 0,0,1,0; 0,-1,0,0; -1,0,0,0]

private theorem UpperTheory.V.Ws.pairJ_sq (k : Type) [Field k] : pairJ k * pairJ k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem UpperTheory.V.Ws.pairJ_adj {k : Type} [Field k] (X : M4 k) :
    X.transpose * pairJ k = pairJ k * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.auPair :
    ∀ {k Γ : Type} [Field k] [Group Γ] (r : Γ →* M4 k) (μ : Γ →* kˣ), (∀ g, IsGSp (μ g : k) (r g)) → ∀ c : Γ, ∃ P : GL (Fin 4) k, ∀ s : Γ, (r s).transpose * (P : M4 k) * r (c * s * c⁻¹) = (μ s : k) • (P : M4 k) := by
  intro k Γ _ _ r μ h c
  refine ⟨⟨pairJ k * r c⁻¹, -(r c * pairJ k), ?_, ?_⟩, fun s => ?_⟩
  · rw [mul_neg, mul_assoc, ← mul_assoc (r c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul, pairJ_sq, neg_neg]
  · rw [neg_mul, mul_assoc, ← mul_assoc (pairJ k), pairJ_sq, neg_mul, one_mul, mul_neg, neg_neg, ← map_mul,
      mul_inv_cancel, map_one]
  · show (r s).transpose * (pairJ k * r c⁻¹) * r (c * s * c⁻¹) = (μ s : k) • (pairJ k * r c⁻¹)
    have e : r c⁻¹ * r (c * s * c⁻¹) = r s * r c⁻¹ := by
      rw [← map_mul, ← map_mul]; congr 1; group
    have hs : adj (r s) * r s = (μ s : k) • (1 : M4 k) := h s
    rw [mul_assoc, mul_assoc, e, ← mul_assoc, pairJ_adj, mul_assoc, ← mul_assoc (adj _), hs,
      smul_mul_assoc, one_mul, mul_smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem psi_map' {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R')
    (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  have hadj : adj ((P.n v).map f) = (adj (P.n v)).map f := by
    ext a b
    simp [adj_apply, Matrix.map_apply, map_zsmul]
  have hr : (mapRep f P.r) s = (P.r s).map f := by
    ext a b
    simp [mapRep_apply]
  change (adj ((P.n v).map f) * (mapRep f P.r) s * (P.n v).map f) i i = f ((adj (P.n v) * P.r s * P.n v) i i)
  rw [hadj, hr, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

theorem UpperTheory.V.Ws.auPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ (y : X.A →ₐ[c'.O] PadicAlgCl l) (x : B.Pt), (∀ b, x b = y (algebraMap X.B X.A (φ b))) → ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) ∧ ((g : G T.L Ω) ∈ Ine (F := T.L) (K.s.A v) → resLe T.F_le g ∈ Ine (F := T.F) (T.pl (K.e v))) ∧ ((x.psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = algebraMap c'.O (PadicAlgCl l) (K.κ g * K.β g ^ n) * (X.P.map (y : X.A →+* PadicAlgCl l)).ψ (K.e v) i (resLe T.F_le g) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y x hx v i g
  have hd : resLe T.F_le g ∈ Dec (F := T.F) (T.pl (K.e v)) := by
    rw [← K.hA v]; exact g.2
  refine ⟨hd, fun hg => by rw [← K.hA v]; exact hg, ?_⟩
  have h1 : ((x.psi v i g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = x (B.u.ψ v i g : B.B) := rfl
  rw [h1, hx, hφ.2 v i g, map_mul, map_mul, X.ψ_map _ _ _ hd, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  exact congrArg _ (psi_map' X.P (y : X.A →+* PadicAlgCl l) (K.e v) i _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.SupComm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem comm_mem {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (F : IntermediateField k Ω) [Normal k F]
    (hc : ∀ a b : F ≃ₐ[k] F, a * b = b * a) (g h : Ω ≃ₐ[k] Ω) : g * h * (h * g)⁻¹ ∈ F.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one, hc]

private theorem sup_comm' {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [Normal k Ω] (F K : IntermediateField k Ω)
    [Normal k F] [Normal k K] (hF : ∀ a b : F ≃ₐ[k] F, a * b = b * a) (hK : ∀ a b : K ≃ₐ[k] K, a * b = b * a)
    (a b : ↥(F ⊔ K) ≃ₐ[k] ↥(F ⊔ K)) : a * b = b * a := by
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥(F ⊔ K)) Ω a
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥(F ⊔ K)) Ω b
  have : g * h * (h * g)⁻¹ ∈ (F ⊔ K).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨comm_mem F hF g h, comm_mem K hK g h⟩
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one] at this
  exact this

theorem UpperTheory.V.Ws.auGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), IsGalois ℚ T.L ∧ IsSolvable (T.L ≃ₐ[ℚ] T.L) := by
  intro Ω _ _ _ l _ c D T
  haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
  haveI hK : IsGalois ℚ T.K := inferInstance
  haveI : IsCyclic (T.K ≃ₐ[ℚ] T.K) := inferInstance
  haveI hF : IsGalois ℚ T.F := inferInstance
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  have hN : Normal ℚ ↥(T.F ⊔ T.K) := @IntermediateField.normal_sup ℚ Ω _ _ _ T.F T.K hF.to_normal hK.to_normal
  have hc := @sup_comm' ℚ Ω _ _ _ _ T.F T.K hF.to_normal hK.to_normal (fun a b => T.abF.is_comm.comm a b)
    (fun a b => (IsAbelianGalois.of_isCyclic ℚ T.K).is_comm.comm a b)
  rw [← T.hL] at hN hc
  exact ⟨{ to_isSeparable := inferInstance, to_normal := hN }, isSolvable_of_comm hc⟩
end

