module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply, RingHom.mapMatrix_apply]

private theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at h ⊢
  have h2 := congrArg f.mapMatrix h
  rw [map_mul, smul_map', map_one, ← adj_map'] at h2
  exact h2

private theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

private theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

private theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps]
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [prj_map, e, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  unfold Raw.condL at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    intro g
    ext a b
    rw [Lift.map_hom]
    rfl
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hr (fun i g => (f.commutes _).symm) h2⟩
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h1 g)

private theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

private theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hr : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    rw [Lift.map_hom]
    rfl
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

private theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

private theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Lift.map_hom, map_add (f := _), map_mul, f.commutes]

private theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := by
  apply Lift.ext
  rfl

private theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

private theorem onComp_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {P : Cond O rbar} {ρ₀ : Γ →* Matrix ι ι O}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {r : Lift O rbar R} (h : OnComp P ρ₀ r) : OnComp P ρ₀ (r.map f) := by
  obtain ⟨B, i1, i2, i3, i4, ρ', hP, hρ, y, hy⟩ := h
  refine ⟨B, i1, i2, i3, i4, ρ', hP, hρ, f.comp y, ?_⟩
  subst hy
  apply Lift.ext
  ext g a b
  simp [Lift.map_hom]

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), (D.IsPt ρ → D.IsEq ρ) ∧ ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (f : R →ₐ[c.O] R'), (D.IsPt ρ → D.IsPt (ρ.map f)) ∧ (D.IsEq ρ → D.IsEq (ρ.map f)) := by
  intro Ω _ _ _ l _ c D _ R _ _ _ ρ
  have hL : ∀ {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt l) S),
      OnComp D.condL (D.r0At l) r → D.condL S r := by
    intro S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hP, _, y, rfl⟩ := hr
    exact condL_map D y ρ' hP
  have hP : ∀ (p : ℕ) {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt p) S),
      OnComp (D.condP p) (D.r0At p) r → D.condP p S r := by
    intro p S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hQ, _, y, rfl⟩ := hr
    exact condP_map D p y ρ' hQ
  refine ⟨fun h => ⟨h.mult, h.unr, h.nrm, hL _ h.atL, fun p hp => hP p _ (h.atP p hp)⟩, ?_⟩
  intro R' _ _ _ f
  refine ⟨fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩,
    fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩⟩
  · rw [loc_map]
    exact onComp_map f h.atL
  · rw [loc_map]
    exact onComp_map f (h.atP p hp)
  · rw [loc_map]
    exact condL_map D f _ h.atL
  · rw [loc_map]
    exact condP_map D p f _ (h.atP p hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_diag {K : Type} [Field K] (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (h : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c :=
  _root_.UpperTheory.Reformulated.B.OrderedFlagDiagonal.ordFlag_diag c hc X h

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_aeval {K : Type} [Field K] (c : Fin 4 → K) (X P : M4 K)
    (h : X * P = P * Matrix.diagonal c) (p : Polynomial K) :
    Polynomial.aeval X p * P = P * Matrix.diagonal fun k => p.eval (c k) := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i j
    simp [Matrix.mul_diagonal, Algebra.algebraMap_eq_smul_one, mul_comm]
  | add p q hp hq =>
    rw [map_add (f := _), add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]
    simp
  | monomial n a hn =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_assoc, h, ← mul_assoc, hn, mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag :
    ∀ {H : Type} [Group H] (I : Subgroup H) (K : Type) [Field K] (ps : Fin 4 → H → K) (s₀ : H) (r : H →* M4 K), Function.Injective (fun i => ps i s₀) → Ord I ps s₀ r → ∃ (u : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ), (∀ g i j, j < i → ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i j = 0) ∧ (∀ g i, ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i i = κ i g) ∧ (∀ i, ∀ s ∈ I, (κ i s : K) = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (κ i g : K) = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H _ I K _ ps s₀ r hc ho
  obtain ⟨P, hP⟩ := ordFlag_diag _ hc (r s₀) ho.charpoly
  set d : Fin 4 → K := fun i => ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀) with hd
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e => (Finset.mem_erase.mp hj).1 (hc e).symm
  have hprj : ∀ i, prj (fun a => ps a s₀) (r s₀) i
      = (P : M4 K) * Matrix.diagonal (Pi.single i (d i)) * ((P⁻¹ : (M4 K)ˣ) : M4 K) := by
    intro i
    rw [Units.eq_mul_inv_iff_mul_eq, prj, ordFlag_aeval _ _ _ hP]
    congr 2
    funext k
    rw [Polynomial.eval_prod]
    by_cases hk : k = i
    · subst hk; simp [hd]
    · rw [Pi.single_eq_of_ne hk]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (by simp)
  have key : ∀ (Y : M4 K) i j, prj (fun a => ps a s₀) (r s₀) i * Y * prj (fun a => ps a s₀) (r s₀) j = 0 →
      (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) i j = 0 := by
    intro Y i j h
    have h2 : Matrix.diagonal (Pi.single i (d i)) * (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) *
        Matrix.diagonal (Pi.single j (d j)) = 0 := by
      have := congrArg (fun Z : M4 K => ((P⁻¹ : (M4 K)ˣ) : M4 K) * Z * (P : M4 K)) h
      simpa [hprj, mul_assoc] using this
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
    simpa [hd0] using h3
  set M : H → M4 K := fun g => ((P⁻¹ : (M4 K)ˣ) : M4 K) * r g * (P : M4 K) with hM
  have htri : ∀ g i j, j < i → M g i j = 0 := fun g i j hij => key _ i j (ho.stable g j i hij)
  have hmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp [hM, mul_assoc]
  let κ₀ : Fin 4 → H →* K := fun i =>
    { toFun := fun g => M g i i
      map_one' := by simp [hM]
      map_mul' := by
        intro g h
        rw [hmul, Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [htri g i k hk, zero_mul]
        · rw [htri h k i hk, mul_zero] }
  refine ⟨P⁻¹, fun i => (κ₀ i).toHomUnits, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [inv_inv]
    exact htri g i j hij
  · intro g i
    rw [inv_inv]
    rfl
  · intro i s hs
    have h1 := key _ i i (ho.inert s hs i)
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul, Matrix.sub_apply, sub_eq_zero] at h1
    show M s i i = _
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    exact h1
  · intro i g
    show d i * M g i i = _
    rw [hprj, mul_assoc, mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    show _ = (Matrix.diagonal (Pi.single i (d i)) * M g).trace
    simp [Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PrimeTo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_modEq_one (l d : ℕ) (hd : d ≠ 0) (h : l.Coprime d) :
    ∀ᶠ n : ℕ in Filter.atTop, l ^ n.factorial ≡ 1 [MOD d] := by
  filter_upwards [Filter.eventually_ge_atTop d.totient] with n hn
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd)) hn
  rw [hk, pow_mul]
  simpa using (Nat.ModEq.pow_totient h).pow k

private theorem pt_dvd (l a : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, l ^ a ∣ l ^ n.factorial := by
  filter_upwards [Filter.eventually_ge_atTop a] with n hn
  exact pow_dvd_pow _ (hn.trans (Nat.self_le_factorial n))

private theorem pt_const (l : ℕ) (hl : l.Prime) {H : Type} [Group H] [Finite H] (x : H) :
    ∃ y, ∀ᶠ n : ℕ in Filter.atTop, x ^ l ^ n.factorial = y := by
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, d, hnd, hod⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.one_lt.ne'
  have hcop : l.Coprime d := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
  have hd : d ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hod)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((pt_modEq_one l d hd hcop).and (pt_dvd l a))
  refine ⟨x ^ l ^ N.factorial, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [pow_eq_pow_iff_modEq, hod, ← Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow_left a hcop)]
  obtain ⟨h1, h2⟩ := hN n hn
  obtain ⟨h1', h2'⟩ := hN N le_rfl
  exact ⟨(Nat.modEq_zero_iff_dvd.2 h2).trans (Nat.modEq_zero_iff_dvd.2 h2').symm, h1.trans h1'.symm⟩

private theorem pt_exists (l : ℕ) (hl : l.Prime) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (g : Γ) :
    ∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') := by
  obtain ⟨g', -, hg'⟩ : ∃ g' ∈ Set.univ, ClusterPt g' (Filter.map (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop) :=
    isCompact_univ.exists_clusterPt (Filter.le_principal_iff.2 Filter.univ_mem)
  refine ⟨g', ?_⟩
  rw [(nhds_basis_opens g').tendsto_right_iff]
  rintro V ⟨hgV, hVo⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hVo.preimage (continuous_const_mul g')) (by simpa using hgV)
  haveI : H.toSubgroup.Normal := H.isNormal'
  haveI : Finite (Γ ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  obtain ⟨y, hy⟩ := pt_const l hl (QuotientGroup.mk (s := H.toSubgroup) g)
  have hnh : ∀ᶠ z in nhds g', g'⁻¹ * z ∈ H.toSubgroup := by
    have hc : Continuous (fun z : Γ => g'⁻¹ * z) := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds (H.isOpen'.mem_nhds ?_)
    show g'⁻¹ * g' ∈ H.toSubgroup
    rw [inv_mul_cancel]
    exact H.toSubgroup.one_mem
  have hfr := hg'.frequently hnh
  rw [Filter.frequently_map] at hfr
  obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually hy).exists
  have hy' : y = QuotientGroup.mk g' := by
    rw [← hn2, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]
    exact hn1
  filter_upwards [hy] with m hm
  rw [hy', ← QuotientGroup.mk_pow, QuotientGroup.eq] at hm
  have := hH (H.toSubgroup.inv_mem hm)
  simpa using this

private theorem pt_step {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I J : Ideal R) (hJ : J ≤ I) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ J) : ∀ a b, (X ^ l - 1) a b ∈ I * J := by
  classical
  have hXi : ∀ i : ℕ, ∀ a b, (X ^ i - 1 : Matrix ι ι R) a b ∈ J := by
    intro i
    have h0 : (Ideal.Quotient.mk J).mapMatrix (X - 1) = 0 := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hX a b
    have h1 : (Ideal.Quotient.mk J).mapMatrix X = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at h0
      exact h0
    have h2 : (Ideal.Quotient.mk J).mapMatrix (X ^ i - 1) = 0 := by
      rw [map_sub, map_pow, h1, one_pow, map_one, sub_self]
    intro a b
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hgeom : X ^ l - 1 = (X - 1) * ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_one, add_sub_cancel, mul_geom_sum]
  intro a b
  rw [hgeom, Matrix.mul_apply]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  have hW : ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) c b ∈ I := by
    rw [Matrix.add_apply, Matrix.sum_apply]
    refine I.add_mem ?_ (I.sum_mem fun i _ => hJ (hXi i c b))
    by_cases hcb : c = b <;> simp [hcb, hl, Matrix.natCast_apply]
  rw [mul_comm ((X - 1) a c)]
  exact Ideal.mul_mem_mul hW (hX a c)

private theorem pt_pow {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I : Ideal R) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ I) (k : ℕ) :
    ∀ a b, (X ^ l ^ k - 1) a b ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hX
  | succ k ih =>
    intro a b
    have h := pt_step I (I ^ (k + 1)) (Ideal.pow_le_self (Nat.succ_ne_zero k)) l hl (X ^ l ^ k) ih a b
    rw [← pow_mul, ← pow_succ] at h
    rw [pow_succ' I (k + 1)]
    exact h

theorem UpperTheory.V.GradeZeroInterpolatingElement.primeTo :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ] (g : Γ), (∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g')) ∧ ∀ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') → ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (ι : Type) [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (m : ℕ), l.Coprime m → rbar g ^ m = 1 → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), rbar g' = rbar g ∧ ρ.hom g' ^ m = 1 := by
  intro l _ Γ _ _ _ _ _ _ g
  have hl : l.Prime := Fact.out
  refine ⟨pt_exists l hl Γ g, ?_⟩
  intro g' hlim O _ _ _ _ ι _ _ rbar m hcop hgm R _ _ _ ρ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_right l |>.1 hcop)
  have key : ∀ {M : Type} [Monoid M] (x : M) (k : ℕ), x ^ m = 1 → k ≡ 1 [MOD m] → x ^ k = x := by
    intro M _ x k hx hk
    have hk' : k % orderOf x = 1 % orderOf x := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) hk
    rw [← pow_mod_orderOf, hk', pow_mod_orderOf, pow_one]
  have hcong := pt_modEq_one l m hm0 hcop
  have hloc : ∀ N : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom (g ^ l ^ n.factorial)) =
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom g') := by
    intro N
    have h1 : ∀ᶠ y in nhds g', ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom y a b) =
        Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom g' a b) := by
      simp only [Filter.eventually_all]
      intro a b
      exact (ρ.cont a b N).eventually_eq g'
    filter_upwards [hlim.eventually h1] with n hn
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hn a b
  have hres : ∀ x y : R, Ideal.Quotient.mk (maximalIdeal R ^ 1) x = Ideal.Quotient.mk (maximalIdeal R ^ 1) y →
      res O R x = res O R y := by
    intro x y h
    rw [Ideal.Quotient.eq, pow_one] at h
    rw [← sub_eq_zero, ← map_sub]
    exact (res_eq_zero_iff O R _).2 h
  have hA : rbar g' = rbar g := by
    obtain ⟨n, hn1, hn2⟩ := ((hloc 1).and hcong).exists
    ext a b
    rw [← ρ.red g' a b]
    have e1 := congrFun (congrFun hn1 a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    rw [← hres _ _ e1, ρ.red, map_pow, key (rbar g) _ hgm hn2]
  have hlM : ((l : ℕ) : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hX : ∀ a b, ((ρ.hom g) ^ m - 1) a b ∈ maximalIdeal R := by
    intro a b
    rw [← res_eq_zero_iff O R, Matrix.sub_apply, map_sub, ← map_pow, ρ.red, map_pow, hgm]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hB : ∀ N : ℕ, ∀ a b, ((ρ.hom g') ^ m - 1) a b ∈ maximalIdeal R ^ N := by
    intro N
    have hfin : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n.factorial + 1 := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact hn.trans ((Nat.self_le_factorial n).trans (Nat.le_succ _))
    obtain ⟨n, hn1, hn2⟩ := ((hloc N).and hfin).exists
    have hp := pt_pow (maximalIdeal R) l hlM _ hX n.factorial
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (((ρ.hom g) ^ m) ^ l ^ n.factorial) = 1 := by
      rw [← sub_eq_zero, ← map_one ((Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix), ← map_sub]
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right hn2 (hp a b)
    have e : (ρ.hom (g ^ l ^ n.factorial)) ^ m = ((ρ.hom g) ^ m) ^ l ^ n.factorial := by
      rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    have hr : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m) = 1 := by
      rw [map_pow, ← hn1, ← map_pow, e]
      exact hq
    intro a b
    have h2 : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m - 1) = 0 := by
      rw [map_sub, hr, map_one, sub_self]
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  refine ⟨hA, ?_⟩
  have hbot : ⨅ i : ℕ, maximalIdeal R ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  rw [← sub_eq_zero]
  ext a b
  have hmem : ((ρ.hom g') ^ m - 1) a b ∈ ⨅ i : ℕ, maximalIdeal R ^ i := Ideal.mem_iInf.2 (fun N => hB N a b)
  rw [hbot, Ideal.mem_bot] at hmem
  rw [Matrix.zero_apply]
  exact hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SixBlock
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit {R : Type} [CommRing R] [IsLocalRing R] {ν a w p h : R} (hν : IsUnit ν)
    (hp : p ∈ maximalIdeal R) (e : a * w - p * h = ν) : IsUnit a := by
  have hu : IsUnit (a * w) := by
    have hx : a * w = ν + p * h := by rw [← e]; ring
    rw [hx]
    by_contra hn
    have h1 : ν + p * h ∈ maximalIdeal R := (mem_maximalIdeal _).2 hn
    have h2 : p * h ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hp
    have h3 : ν ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ h1 h2
    exact (mem_maximalIdeal _).1 h3 hν
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.V.GradeZeroInterpolatingElement.sixBlock :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (ν : R) (g : M4 R), IsUnit ν → IsGSp ν g → (∀ i j, i ≠ j → g i j ∈ maximalIdeal R) → g 0 1 = 0 → g 0 3 = 0 → g 2 1 = 0 → g 1 0 = 0 → g 3 0 = 0 → g 1 2 = 0 → IsBlock g ∧ (ν = 1 → g 0 2 = 0 → g 2 0 = 0 → g 0 0 = 1 → g 1 1 = 1 → g = 1) := by
  intro R _ _ ν g hν hg hoff h01 h03 h21 h10 h30 h12
  have hg' : adj g * g = ν • 1 := hg
  have E : ∀ i j, (adj g * g) i j = (ν • (1 : M4 R)) i j := fun i j => by rw [hg']
  have errorNonneg := E 0 0
  have bivariateExponentMonomial := E 0 1
  have E11 := E 1 1
  have E10 := E 1 0
  have E13 := E 1 3
  have E20 := E 2 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, h01, h03, h21, h10, h30, h12,
    Matrix.one_apply] at errorNonneg bivariateExponentMonomial E11 E10 E13 E20
  have u00 : IsUnit (g 0 0) :=
    UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit (w := g 3 3) (h := g 2 0) hν (hoff 1 3 (by decide)) (by rw [← errorNonneg]; ring)
  have u11 : IsUnit (g 1 1) :=
    UpperTheory.V.GradeZeroInterpolatingElement.sixBlock_unit (w := g 2 2) (h := g 3 1) hν (hoff 0 2 (by decide)) (by rw [← E11]; ring)
  have h23 : g 2 3 = 0 := u11.mul_left_eq_zero.1 bivariateExponentMonomial
  have h32 : g 3 2 = 0 := u00.mul_left_eq_zero.1 E10
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [lamW, h01, h03, h21, h23, h10, h12, h30, h32] at hij ⊢
  · intro hν1 h02 h20 h00 h11
    subst hν1
    have h22 : g 2 2 = 1 := by simpa [h11, h02] using E11
    have h33 : g 3 3 = 1 := by simpa [h00, h20] using errorNonneg
    have h13 : g 1 3 = 0 := by simpa [h22, h02] using E13
    have h31 : g 3 1 = 0 := by simpa [h11, h20, h00] using E20
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]
end

