module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Pt.cycIne :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ n : ℤ, n ≠ 0 → ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ A hA n hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  let ι : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp ι
  haveI : Finite (F →ₐ[ℚ] Ω) := inferInstance
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt hfe
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, fun x => ?_⟩
    have h1 : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) hfe
    have h2 : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [h2, AlgEquiv.mul_apply] at h1
    exact ((σ ^ a).injective h1).symm
  obtain ⟨N, hN, hfix⟩ : ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h he
    · exact key b a h he.symm
  let g : G F Ω := AlgEquiv.ofRingEquiv (f := (σ ^ N).toRingEquiv) hfix
  have hg : (g.restrictScalars ℚ : G ℚ Ω) = σ ^ N := AlgEquiv.ext fun y => rfl
  have hφinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)).toMonoidHom := by
    show Function.Injective (algebraMap ℤ_[l] (Qbar l))
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)
  have hinj : Function.Injective (Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom) :=
    Units.map_injective hφinj
  refine ⟨g, ?_, ?_⟩
  · show (g.restrictScalars ℚ : G ℚ Ω) ∈ Ine (F := ℚ) A
    rw [hg]
    exact Subgroup.pow_mem _ hσI N
  · have hc : cycBar F Ω l g =
        Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom (cycZ ℚ Ω l (g.restrictScalars ℚ)) := rfl
    rw [hc, hg, map_pow, hσu]
    intro h
    apply hu ((N : ℤ) * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn)
    rw [zpow_mul, zpow_natCast]
    apply hinj
    rw [map_zpow, map_one]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ExistsResLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem exists_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) (hg : g ∈ T.GalL) : ∃ s : G T.L Ω, resLe T.F_le s = g := by
  have h1 : resQ T.F g ∈ T.K.fixingSubgroup := hg
  have h2 : resQ T.F g ∈ T.F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
  have h3 : resQ T.F g ∈ T.L.fixingSubgroup := by
    have e : T.L.fixingSubgroup = T.F.fixingSubgroup ⊓ T.K.fixingSubgroup := by
      rw [T.hL]; exact IntermediateField.fixingSubgroup_sup
    rw [e]
    exact ⟨h2, h1⟩
  have h4 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h3
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h4 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

theorem UpperTheory.V.Ws.Pt.ptIrr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), Irr (r.comp T.G'.subtype) → Irr r ∧ Af.IsIrr ((K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype) := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  constructor
  · have h1 : Submodule.span (PadicAlgCl l) (Set.range (r.comp T.G'.subtype)) = ⊤ := hr
    change Submodule.span (PadicAlgCl l) (Set.range r) = ⊤
    refine eq_top_iff.2 (h1.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · have h2 := (auIrr (r.comp T.G'.subtype) ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype) hr ?_).2
      ((K.twc n).comp (cycBar T.L Ω l).ker.subtype)
    · have e : (K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype =
          Af.tw ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype).toHomUnits
            ((K.twc n).comp (cycBar T.L Ω l).ker.subtype) := by
        refine MonoidHom.ext fun g => Units.ext ?_
        rw [Af.tw_val]
        exact K.rho_val n r g
      rw [e]
      exact h2
    · intro g
      obtain ⟨s, hs⟩ := exists_resLe T g.1 g.2.1
      have hz : cycZ T.F Ω l g.1 = 1 := g.2.2
      have hk : s ∈ (cycBar T.L Ω l).ker := by
        rw [MonoidHom.mem_ker, ← cycBar_resLe T.F_le, hs, cycBar, MonoidHom.comp_apply, hz, map_one]
      refine ⟨⟨s, hk⟩, ?_⟩
      change r (resLe T.F_le s) = r g.1
      rw [hs]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PtFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem ptFlag_adj_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : M4 R) :
    adj (u.map f) = (adj u).map f := by
  ext i j
  simp only [Matrix.map_apply, adj_apply]
  rw [map_zsmul]

theorem UpperTheory.V.Ws.Pt.ptFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp (Dec (F := T.L) (K.s.A v)).subtype) ((Link.pt φ y).psi v) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y v
  have hpair := X.pair
  have hlow := hpair.low (K.e v)
  have hadj : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := Pp.adj_mul_self hlow.1
  have hr : ∀ t, (X.P.map (y : X.A →+* PadicAlgCl l)).r t = (X.P.r t).map (y : X.A →+* PadicAlgCl l) :=
    fun t => rfl
  have hu : adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) = 1 := by
    rw [ptFlag_adj_map, ← Matrix.map_mul, hadj,
      Matrix.map_one _ (map_zero (y : X.A →+* PadicAlgCl l)) (map_one (y : X.A →+* PadicAlgCl l))]
  have hu' := mul_eq_one_comm.mp hu
  have hM : ∀ t, adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.r t).map (y : X.A →+* PadicAlgCl l) * (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)
      = (adj (X.P.n (K.e v)) * X.P.r t * X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) := by
    intro t
    rw [ptFlag_adj_map, Matrix.map_mul, Matrix.map_mul]
  refine ⟨⟨_, _, hu, hu'⟩, fun s => ?_⟩
  have hs : resLe T.F_le (s : G T.L Ω) ∈ Dec (T.pl (K.e v)) := by
    rw [resLe_mem_Dec, ← K.hA v]
    exact s.2
  have hval : (((⟨_, _, hu, hu'⟩ * ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp
      (Dec (F := T.L) (K.s.A v)).subtype) s * (⟨_, _, hu, hu'⟩)⁻¹ : GL (Fin 4) (PadicAlgCl l))) :
        Matrix (Fin 4) (Fin 4) (PadicAlgCl l))
      = (((K.twc n) (s : G T.L Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) •
        (adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
          (X.P.r (resLe T.F_le (s : G T.L Ω))).map (y : X.A →+* PadicAlgCl l) *
          (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) := by
    rw [Units.val_mul, Units.val_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, Link.rho_val, hr]
    simp only [Units.inv_mk, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, hM, Matrix.map_apply, hpair.flag (K.e v) _ hs i j hij, map_zero, smul_zero]
  · rw [hval, Matrix.smul_apply, hφ.psi_val y v i s hs, smul_eq_mul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PtPair
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_adj {R : Type} [CommRing R] (X : M4 R) : formJ R * adj X = X.transpose * formJ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

private theorem formJ_sq (R : Type) [CommRing R] : formJ R * formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private def formU (R : Type) [CommRing R] : GL (Fin 4) R :=
  ⟨formJ R, -formJ R, by rw [mul_neg, formJ_sq, neg_neg], by rw [neg_mul, formJ_sq, neg_neg]⟩

private theorem form_gsp {R : Type} [CommRing R] {ν : R} {X : M4 R} (hX : IsGSp ν X) :
    X.transpose * formJ R * X = ν • formJ R := by
  have hX' : adj X * X = ν • 1 := hX
  rw [← formJ_adj, Matrix.mul_assoc, hX', Matrix.mul_smul, Matrix.mul_one]

theorem UpperTheory.V.Ws.Pt.ptPair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∃ P : GL (Fin 4) (PadicAlgCl l), Af.IsPairing K.s.c (K.rhoQ n r) (cycBar T.L Ω l ^ (1 - ((4 : ℕ) : ℤ))) P := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  obtain ⟨j, hj⟩ := K.s.hc
  have hfixF : ∀ x : T.F, K.s.c (algebraMap T.F Ω x) = algebraMap T.F Ω x := by
    intro x
    apply j.injective
    rw [hj]
    have hw := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap T.F Ω)))
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hw
    have hx := RingHom.congr_fun hw x
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := K.s.c.toRingEquiv) hfixF
  have hCiC : r cF⁻¹ * r cF = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hCCi : r cF * r cF⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  let U : GL (Fin 4) (PadicAlgCl l) := ⟨r cF⁻¹, r cF, hCiC, hCCi⟩
  refine ⟨formU (PadicAlgCl l) * U, ?_⟩
  intro s s' hs
  have hres : resLe T.F_le s' = cF * resLe T.F_le s * cF⁻¹ := by
    ext x
    have hx := DFunLike.congr_fun hs x
    first
      | exact hx
      | simpa [cF] using hx
  have hconj := K.conj s s' hs
  rw [K.rho_val, K.rho_val, hres, map_mul, map_mul]
  have hA := form_gsp (hr (resLe T.F_le s))
  have hU : ((formU (PadicAlgCl l) * U : GL (Fin 4) (PadicAlgCl l)) : M4 (PadicAlgCl l)) =
      formJ (PadicAlgCl l) * r cF⁻¹ := rfl
  rw [hU]
  have key : (r (resLe T.F_le s)).transpose * (formJ (PadicAlgCl l) * r cF⁻¹) *
      (r cF * r (resLe T.F_le s) * r cF⁻¹) =
      ((r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * r (resLe T.F_le s)) * r cF⁻¹ := by
    calc _ = (r (resLe T.F_le s)).transpose * formJ (PadicAlgCl l) * (r cF⁻¹ * r cF) *
          r (resLe T.F_le s) * r cF⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hCiC, Matrix.mul_one]
  rw [hA, Matrix.smul_mul] at key
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [key, smul_smul]
  congr 1
  rw [K.twc_val, K.twc_val, ← map_mul, ← map_mul]
  have hq : resQ T.F (resLe T.F_le s) = resQ T.L s := rfl
  rw [hq]
  have hb : (↑(K.β s) : c'.O) * ↑(K.β s') = 1 := by rw [← Units.val_mul, hconj.2.1, Units.val_one]
  have e1 : (↑(K.κ s') * ↑(K.β s') ^ n : c'.O) * (↑(K.κ s) * ↑(K.β s) ^ n) * inc h ↑(D.th (resQ T.L s)) =
      ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) := by
    calc _ = ↑(K.κ s) * ↑(K.κ s') * inc h ↑(D.th (resQ T.L s)) * (↑(K.β s) * ↑(K.β s')) ^ n := by ring
      _ = _ := by rw [hb, one_pow, mul_one]
  rw [e1]
  have e3 := congrArg (algebraMap c'.O (PadicAlgCl l)) hconj.1
  rw [map_mul, map_pow, map_one] at e3
  have hχ : algebraMap c'.O (PadicAlgCl l) ↑((chiO T.L Ω l c'.O) s) = (↑(cycBar T.L Ω l s) : PadicAlgCl l) := rfl
  rw [hχ] at e3
  rw [eq_inv_of_mul_eq_one_left e3]
  have hz : (1 - ((4 : ℕ) : ℤ)) = -3 := by norm_num
  rw [hz]
  first
    | simp [zpow_neg, Units.val_zpow_eq_zpow_val]
    | (rw [MonoidHom.zpow_apply]; simp [zpow_neg, Units.val_zpow_eq_zpow_val])
    | done
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResOneOfMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem eq_one_of_res {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {x : R} {m : ℕ} (hm : IsUnit (m : R))
    (h1 : residue R x = 1) (hx : x ^ m = 1) : x = 1 := by
  have hs : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
    have h0 : residue R (∑ i ∈ Finset.range m, x ^ i) = residue R (m : R) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_pow, h1]
    by_contra hn
    have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal R := hn
    rw [← residue_eq_zero_iff, h0] at hmem
    exact (residue_eq_zero_iff _).mp hmem hm
  have hg := geom_sum_mul x m
  rw [hx, sub_self] at hg
  exact sub_eq_zero.mp ((hs.mul_right_eq_zero).mp hg)

private theorem res_one_of_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) {x : R}
    (h : residue S (f x) = 1) : residue R x = 1 := by
  by_contra hn
  have hu : IsUnit (x - 1) := by
    by_contra hu
    exact hn (sub_eq_zero.mp (by rw [← map_one (residue R), ← map_sub]; exact (residue_eq_zero_iff _).mpr hu))
  have hfu := hu.map f
  rw [map_sub, map_one] at hfu
  have hz : residue S (f x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  exact ((residue_eq_zero_iff _).mp hz) hfu

private theorem not_valuation_natCast_prime_lt_one_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) : ¬ (K.s.A K.s.v0).valuation (l : Ω) < 1 := by
  intro hv
  have hmem : (l : 𝓞 (W.Lp T.L)) ∈ K.s.v0.asIdeal := by
    rw [← K.s.hA K.s.v0 (l : 𝓞 (W.Lp T.L))]
    simpa using hv
  have hmax := K.s.v0.isMaximal
  letI : Field (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = K.s.p := K.s.norm_v0_eq_one
  have hfin : Finite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact K.s.p_prime.ne_zero
  letI := Fintype.ofFinite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal)
  have hp0 : ((K.s.p : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hl0 : ((l : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have h1 := Nat.dvd_gcd (ringChar.dvd hp0) (ringChar.dvd hl0)
  rw [(Nat.coprime_primes K.s.p_prime (Fact.out)).mpr K.s.p_ne] at h1
  have h0 : ((1 : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := (ringChar.spec _ 1).mpr h1
  simp at h0

theorem UpperTheory.V.Ws.Pt.ptUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g ∈ (T.fr ∅).N, r g = 1) → ∀ g ∈ Ine (F := T.L) (K.s.A K.s.v0), K.rhoQ n r g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n r hr g hg
  have hv := not_valuation_natCast_prime_lt_one_link K
  have hβ : K.β g = 1 := K.β_t (K.t_unr _ hv hg)
  obtain ⟨m, hcop, hm⟩ := K.tame
  have hchib : ∀ i, (K.r.chib i) (K.V.pr g) = 1 := fun i => K.v0.1 i (Subgroup.mem_map_of_mem K.V.pr hg)
  have hres : ∀ i, residue c'.O ((K.κ g : c'.O) * inc h ((chi D T.pr i) (resQ T.L g) : c.O)) = 1 := by
    intro i
    rw [← K.chib i g, hchib i, Units.val_one]
  have hi3 : ∃ i, lab T.pr i = 3 := by
    unfold lab
    split
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  have hsurj : ∀ j, ∃ i, lab T.pr i = j := by
    unfold lab
    split
    · decide
    · intro j
      exact ⟨j, rfl⟩
  obtain ⟨i3, hi3⟩ := hi3
  have hκr : residue c'.O (K.κ g : c'.O) = 1 := by
    have h3 := hres i3
    have hc : (chi D T.pr i3) (resQ T.L g) = 1 := by
      simp [chi, hi3, Raw.ps]
    rw [hc, Units.val_one, map_one, mul_one] at h3
    exact h3
  have hκ : K.κ g = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply eq_one_of_res ((dvrFacts l c'.O).2.2.2.2.2.2.2.2 m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)) hκr
    rw [← Units.val_pow_eq_pow_val, hm _ hv g hg, Units.val_one]
  have hps : ∀ j, residue c.O ((D.ps j) (resQ T.L g) : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj j
    apply res_one_of_map (inc h)
    have h4 := hres i
    rw [map_mul, hκr, one_mul] at h4
    rw [← hi]
    exact h4
  have hrbar : D.rbar (resQ T.L g) = 1 := by
    unfold Raw.rbar Raw.r0
    ext a b
    simp only [GradeZeroInterpolatingElement.mapRep, GradeZeroInterpolatingElement.diagRep, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      show ((residue c.O).mapMatrix _) a a = 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact hps a
    · show ((residue c.O).mapMatrix _) a b = 0
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hab, map_zero]
  have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨K.s.A K.s.v0, ?_, (resLe_mem_Ine T.F_le).mpr hg, hrbar⟩
    intro q hq
    have hq' : q = l := by simpa using hq
    subst hq'
    exact hv
  apply Units.ext
  rw [Link.rho_val, hr _ hN, Units.val_one]
  have htw : ((K.twc n) g : PadicAlgCl l) = 1 := by
    rw [Link.twc_val, hκ, hβ]
    simp
  rw [htw, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.TwWts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem aux {M : Type} [CommGroup M] (x y z : M) (a b : ℤ) (k n : ℕ) (h1 : (x * z ^ (-a)) ^ k = 1)
    (h2 : (y ^ 2 * z ^ (-b)) ^ k = 1) : ((x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b))) ^ k = 1 := by
  have e : (x * y ^ n) ^ 2 * z ^ (-(2 * a + n * b)) = (x * z ^ (-a)) ^ 2 * (y ^ 2 * z ^ (-b)) ^ n := by
    simp only [mul_pow, ← zpow_natCast, ← zpow_mul, mul_zpow]
    rw [show -(2 * a + (n:ℤ) * b) = -a * 2 + -b * n by ring, zpow_add]
    push_cast
    rw [mul_comm (n:ℤ) 2]
    ac_rfl
  rw [e, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k, mul_comm n k, pow_mul, pow_mul, h1, h2, one_pow, one_pow,
    one_mul]

theorem UpperTheory.V.Ws.Pt.twWts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ (e : ℤ) (k : ℕ), 0 < k ∧ Even (e + n) ∧ ∀ g ∈ Ine (F := T.L) A, (K.twc n g ^ 2 * cycBar T.L Ω l g ^ (-e)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n A hA
  obtain ⟨a, b, k, hk, hb, hg⟩ := K.cyc A hA
  refine ⟨2 * a + n * b, k, hk, ?_, fun g hgA => ?_⟩
  · obtain ⟨m, rfl⟩ := hb
    exact ⟨a + n * m + n, by ring⟩
  · obtain ⟨h1, h2⟩ := hg g hgA
    have hc : cycBar T.L Ω l g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (chiO T.L Ω l c'.O g) := by
      ext
      change algebraMap ℚ_[l] (PadicAlgCl l) (PadicInt.Coe.ringHom ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
        = algebraMap c'.O (PadicAlgCl l) (algebraMap ℤ_[l] c'.O ((cycZ T.L Ω l g : ℤ_[l]ˣ) : ℤ_[l]))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] c'.O (PadicAlgCl l),
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    have ht : K.twc n g
        = Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l) (K.κ g * K.β g ^ n) := rfl
    rw [hc, ht, ← map_pow, ← map_zpow, ← map_mul, ← map_pow, aux _ _ _ a b k n h1 h2, map_one]
end

