module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LengthLeCotLenOfInjectiveTangentMap
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul' {O σ : Type} [CommRing O] (i : σ) (f g : MvPowerSeries σ O) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + constantCoeff g * coeff (Finsupp.single i 1) f := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  ring

private noncomputable def lin {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] : (σ → Q) →+ (FA O wt →ₗ[O] Q) where
  toFun v :=
    { toFun := fun f => ∑ i, coeff (Finsupp.single i 1) (ser f) • v i
      map_add' := fun f g => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        simp [Finset.smul_sum, mul_smul] }
  map_zero' := by ext f; simp
  map_add' v w := by ext f; simp [Finset.sum_add_distrib]

private theorem lin_apply {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (f : FA O wt) :
    lin wt Q v f = ∑ i, coeff (Finsupp.single i 1) (ser f) • v i := rfl

private theorem lin_zA {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (i : σ) :
    lin wt Q v ((WPres.free O wt).zA i) = v i := by
  classical
  rw [lin_apply]
  have : ser ((WPres.free O wt).zA i) = (X i : MvPowerSeries σ O) := rfl
  rw [this, Finset.sum_eq_single i]
  · simp [coeff_X]
  · intro b _ hb
    rw [coeff_X, if_neg, zero_smul]
    intro h
    exact hb (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.length_le_cotLen_of_injective_tangent_map :
    LemmaM' → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ), j ≠ 0 →
        ∀ (κ : Type) (F : κ → FA O wt), (∀ k, F k ∈ Fgr O wt j) → ∀ c : O, c ≠ 0 →
        ∀ (M : Type) [AddCommGroup M] [Module O M] (d : M →+ (σ → O ⧸ Ideal.span {c})), Function.Injective d →
        (∀ μ i, wt i ≠ j → d μ i = 0) → (∀ μ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) • d μ i = 0) →
        Module.length O M ≤ cotLen (x0 O wt) (Fgr O wt) j F := by
  intro hM O _ _ _ _ σ _ wt j hj κ F hF c hc M _ _ d hd hwt hker
  classical
  let D : M →+ (FA O wt →ₗ[O] O ⧸ Ideal.span {c}) := (lin wt (O ⧸ Ideal.span {c})).comp d
  have hD : ∀ μ f, D μ f = ∑ i, coeff (Finsupp.single i 1) (ser f) • d μ i :=
    fun μ f => lin_apply wt _ (d μ) f
  have hwsingle : ∀ i : σ, (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
    intro i
    simp [Finsupp.weight_apply]
  refine hM O (FA O wt) ℤ (Fgr O wt) (x0 O wt) j ?_ κ F hF c hc M D ?_ ?_ ?_
  · intro f hf
    rw [weightedSeriesOrigin_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (mem_Fgr.mp hf) 0 (by simpa using hj.symm)
  · intro μ ν h
    apply hd
    funext i
    have h2 := congrArg (fun L : FA O wt →ₗ[O] O ⧸ Ideal.span {c} => L ((WPres.free O wt).zA i))
      (congrArg (fun T => T) h)
    simpa [D, lin_zA] using h2
  · intro μ k
    rw [hD]
    exact hker μ k
  · intro μ
    choose e he using fun i => Ideal.Quotient.mk_surjective (d μ i)
    let e' : σ → O := fun i => if wt i = j then e i else 0
    have he' : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (e' i) = d μ i := by
      intro i
      by_cases h : wt i = j
      · simp [e', h, he]
      · simp [e', h, hwt μ i h]
    refine ⟨lin wt O e', ?_, ?_, ?_⟩
    · intro f g
      have hs : ser (f * g) = ser f * ser g := rfl
      rw [lin_apply, lin_apply, lin_apply, weightedSeriesOrigin_apply, weightedSeriesOrigin_apply, hs]
      simp only [coeff_single_mul', smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · intro i' hi' f hf
      rw [lin_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : wt i = j
      · have h0 : coeff (Finsupp.single i 1) (ser f) = 0 := by
          refine (mem_Fgr.mp hf) _ ?_
          rw [hwsingle, h]
          exact fun e => hi' e.symm
        rw [h0, zero_smul]
      · simp [e', h]
    · intro f
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hD, lin_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he' i, smul_eq_mul, map_mul, Algebra.smul_def]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftingObstructionSecondCohomology
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition {O M : Type} [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    [Finite M] (hM : ∀ a ∈ maximalIdeal O, ∀ x : M, a • x = 0) :
    ∃ (n : ℕ) (p : Fin n → M →ₗ[O] ResidueField O) (q : Fin n → ResidueField O →ₗ[O] M),
      ∀ x, ∑ i, q i (p i x) = x := by
  have hT : Module.IsTorsionBySet O M (maximalIdeal O) := fun x a => hM a.1 a.2 x
  letI : Module (ResidueField O) M := hT.module
  haveI : IsScalarTower O (ResidueField O) M := hT.isScalarTower
  haveI : Module.Finite (ResidueField O) M := Module.Finite.of_finite
  let B := Module.finBasis (ResidueField O) M
  refine ⟨_, fun i => (B.coord i).restrictScalars O,
    fun i => (LinearMap.toSpanSingleton (ResidueField O) M (B i)).restrictScalars O, fun x => ?_⟩
  simpa using B.sum_repr x

private theorem UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (X : Matrix (Fin 3) (Fin 3) S) (a b : Fin 3) :
    adRep (r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ)) g X a b =
      ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then X a b else -X b.rev a.rev) := by
  rw [adRep_baseLift_apply, Algebra.smul_def, MonoidHom.comp_apply, ← map_zpow]
  rfl

private theorem UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra {O S D : Type} [CommRing O] [CommRing S] [Algebra O S] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) :
    (GG.map (algebraMap O S)).comp (r0 η Ψ) = r0 η ((Units.map (algebraMap O S).toMonoidHom).comp Ψ) := by
  ext g i j
  · simp [r0, GG.map]
    rw [tor_val, tor_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rw [← map_zpow, ← map_zpow, Units.coe_map, map_zpow]
      rfl
    · simp
  · simp [r0, GG.map]

private theorem UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary {k D : Type} [CommRing k] [Group D] [TopologicalSpace D]
    (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) (h : Subsingleton (H2 (gRep η Ψ j)))
    (κ : D × D → Matrix (Fin 3) (Fin 3) k) (hc : IsLocallyConstant κ) (hw : ∀ z, κ z ∈ gw k j)
    (hκ : ∀ g h l, adRep (r0 η Ψ) g (κ (h, l)) - κ (g * h, l) + κ (g, h * l) - κ (g, h) = 0) :
    ∃ b : D → Matrix (Fin 3) (Fin 3) k, IsLocallyConstant b ∧ (∀ g, b g ∈ gw k j) ∧
      ∀ g h, κ (g, h) = adRep (r0 η Ψ) g (b h) - b (g * h) + b g := by
  let f : D × D → Gb (k := k) j := fun z => (⟨κ z, hw z⟩ : ↥(gw k j))
  have hfl : IsLocallyConstant f :=
    IsLocallyConstant.desc f (fun x : Gb (k := k) j => (x.val : Matrix (Fin 3) (Fin 3) k)) hc
      (fun x y hxy => Subtype.ext hxy)
  have hf : f ∈ Z2 (gRep η Ψ j) := by
    refine (mem_cocycles2 _ _).2 ⟨hfl.continuous, fun g h l => ?_⟩
    apply Subtype.ext
    exact hκ g h l
  have h0 : (Submodule.Quotient.mk ⟨f, hf⟩ : H2 (gRep η Ψ j)) = 0 := Subsingleton.elim _ _
  have hB : f ∈ B2 (gRep η Ψ j) := by
    have := (Submodule.Quotient.mk_eq_zero ((B2 (gRep η Ψ j)).comap (Z2 (gRep η Ψ j)).subtype)
      (x := ⟨f, hf⟩)).1 h0
    simpa using this
  obtain ⟨c, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  refine ⟨fun g => (c g).val, ((IsLocallyConstant.iff_continuous c).2 hcc).comp _,
    fun g => (c g).2, fun g h => ?_⟩
  have e := congrArg (fun x : Gb (k := k) j => x.val) (congrFun hd (g, h))
  rw [d1_apply] at e
  exact e.symm

theorem UpperTheory.V.UnitaryThreeInertia.lifting_obstruction_second_cohomology :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ κ : D × D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant κ → (∀ z, κ z ∈ gw R j) → (∀ z, EntIn K (κ z)) →
      (∀ g h k, adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (κ (h, k)) - κ (g * h, k) + κ (g, h * k) - κ (g, h) = 0) →
      ∃ b : D → Matrix (Fin 3) (Fin 3) R, IsLocallyConstant b ∧ (∀ g, b g ∈ gw R j) ∧ (∀ g, EntIn K (b g)) ∧
        ∀ g h, κ (g, h) = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g (b h) - b (g * h) + b g := by
  classical
  intro O R D _ _ _ _ _ _ _ _ η Ψ K j hK hH κ hc hw hE hκ
  have memgw : ∀ (S : Type) [CommRing S] (X : Matrix (Fin 3) (Fin 3) S),
      X ∈ gw S j ↔ ∀ a b, ¬ wt a b = j → X a b = 0 := by
    intro S _ X
    unfold gw
    rfl
  have hloc : IsLocalHom (algebraMap O R) := by
    obtain ⟨_, hl, _⟩ := ‹IsCO O R›
    exact hl
  let KO : Submodule O R := K.restrictScalars O
  have hM : ∀ a ∈ maximalIdeal O, ∀ x : KO, a • x = 0 := by
    intro a ha x
    apply Subtype.ext
    have h1 : algebraMap O R a ∈ maximalIdeal R := map_nonunit (algebraMap O R) a ha
    have h2 : algebraMap O R a * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul h1 x.2
    rw [hK] at h2
    simpa [Algebra.smul_def] using h2
  obtain ⟨n, p, q, hpq⟩ := UpperTheory.V.UnitaryThreeInertia.residue_coordinates_decomposition hM
  rw [UpperTheory.V.UnitaryThreeInertia.diagonal_rep_map_algebra] at hκ ⊢
  have hE' : ∀ z a b, κ z a b ∈ KO := fun z a b => hE z a b
  let κK : D × D → Fin 3 → Fin 3 → KO := fun z a b => ⟨κ z a b, hE' z a b⟩
  have hres : (Units.map (residue O).toMonoidHom).comp Ψ =
      (Units.map (algebraMap O (ResidueField O)).toMonoidHom).comp Ψ := rfl
  have key : ∀ i, ∃ b : D → Matrix (Fin 3) (Fin 3) (ResidueField O), IsLocallyConstant b ∧
      (∀ g, b g ∈ gw (ResidueField O) j) ∧ ∀ g h, Matrix.of (fun a c => p i (κK (g, h) a c)) =
        adRep (r0 η ((Units.map (residue O).toMonoidHom).comp Ψ)) g (b h) - b (g * h) + b g := by
    intro i
    refine UpperTheory.V.UnitaryThreeInertia.residual_cocycle_is_coboundary η ((Units.map (residue O).toMonoidHom).comp Ψ) j hH
      (fun z => Matrix.of (fun a c => p i (κK z a c))) ?_ ?_ ?_
    · let G : Matrix (Fin 3) (Fin 3) R → Matrix (Fin 3) (Fin 3) (ResidueField O) :=
        fun X => Matrix.of fun a c => if h : X a c ∈ KO then p i ⟨X a c, h⟩ else 0
      have hG : (fun z => Matrix.of (fun a c => p i (κK z a c))) = G ∘ κ := by
        funext z
        ext a c
        simp [G, κK, hE' z a c]
      rw [hG]
      exact hc.comp G
    · intro z
      rw [memgw]
      intro a c hac
      have h0 : κK z a c = 0 := Subtype.ext ((memgw R (κ z)).1 (hw z) a c hac)
      simp [h0]
    · intro g h l
      ext a c
      have e := congrFun (congrFun (hκ g h l) a) c
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, Matrix.of_apply] at e ⊢
      rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] at e
      rw [hres, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
      have eK : ((Ψ g ^ wt a c : Oˣ) : O) • (if η g = 1 then κK (h, l) a c else -κK (h, l) c.rev a.rev) -
          κK (g * h, l) a c + κK (g, h * l) a c - κK (g, h) a c = 0 := by
        apply Subtype.ext
        split_ifs at e ⊢ <;> simpa [κK] using e
      have e2 := congrArg (p i) eK
      split_ifs at e2 ⊢ <;> simpa using e2
  choose bs hbl hbw hbe using key
  refine ⟨fun g => Matrix.of fun a c => ((∑ i, q i (bs i g a c) : KO) : R), ?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Filter.eventually_all.2 (fun i => (hbl i).eventually_eq x)] with y hy
    simp only [hy]
  · intro g
    rw [memgw]
    intro a c hac
    have h0 : ∀ i, bs i g a c = 0 := fun i => (memgw _ _).1 (hbw i g) a c hac
    simp [h0]
  · intro g
    unfold EntIn
    intro a c
    exact (∑ i, q i (bs i g a c)).2
  · intro g h
    ext a c
    have e : ∀ i, p i (κK (g, h) a c) = ((Ψ g ^ wt a c : Oˣ) : O) •
        (if η g = 1 then bs i h a c else -bs i h c.rev a.rev) - bs i (g * h) a c + bs i g a c := by
      intro i
      have e1 := congrFun (congrFun (hbe i g h) a) c
      rw [hres] at e1
      simpa only [Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply] using e1
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [UpperTheory.V.UnitaryThreeInertia.adjoint_diagonal_rep_apply]
    simp only [Matrix.of_apply]
    have hx : κ (g, h) a c = ((κK (g, h) a c : KO) : R) := rfl
    rw [hx, ← hpq (κK (g, h) a c)]
    simp_rw [e]
    split_ifs <;> simp [map_add (f := _), map_sub, map_neg, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtPushOfLocAt
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp only [GG.map, GG.ofGL, SemidirectProduct.map_inl]

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply,
    map_mul, map_inv, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (((GG.map (φ : R →+* R')).comp r)) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]
  simp [GG.mat, GG.map, SemidirectProduct.map_left]

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨?_, ?_⟩
  · intro g hg a b hab
    rw [conj_push_mat, H.tri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, H.ine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I ((GG.map (φ : R →+* R')).comp r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  refine ⟨triIn_push φ H.toTriIn, ?_⟩
  intro g hg a b hab
  rw [conj_push_mat, H.low g hg a b hab, map_zero]

variable [IsLocalRing O] [IsCO O R] [IsCO O R']

private theorem inHat_push (φ : R →ₐ[O] R') {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  have hm : ∀ x ∈ maximalIdeal R, φ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  unfold InHat CongOne EntIn at H ⊢
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    by_cases hab : a = b <;> simp [Matrix.sub_apply, hab]
  rw [e]
  exact hm _ (H a b)

end SlopeTestRemainingChoices

theorem UpperTheory.locAt_push_of_locAt :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (φ : R →ₐ[O] R') (v : ι) (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (((GG.map (φ : R →+* R')).comp r)) := by
  intro O _ _ G Γ ι _ _ F R R' _ _ _ _ _ _ φ v r hr
  unfold Frame.LocAt at hr ⊢
  obtain ⟨hT, hD, hU⟩ := hr
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨h, hh, ht⟩ := hT hv
    exact ⟨_, inHat_push φ hh, triIn_push φ ht⟩
  · obtain ⟨h, hh, ht⟩ := hD hv
    exact ⟨_, inHat_push φ hh, diagIn_push φ ht⟩
  · intro s hs
    have h1 := hU hv s hs
    simp only [MonoidHom.comp_apply, h1, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtDiag
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private def Up (g : GL (Fin 3) R) : Prop := Matrix.BlockTriangular (g : Matrix (Fin 3) (Fin 3) R) id

private theorem ltd_wt_neg_iff (a b : Fin 3) : wt a b < 0 ↔ b < a := by
  revert a b; decide

private theorem Up.mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) : Up (g * h) :=
  Matrix.BlockTriangular.mul hg hh

private theorem Up.inv {g : GL (Fin 3) R} (hg : Up g) : Up g⁻¹ := by
  letI : Invertible (g : Matrix (Fin 3) (Fin 3) R) := g.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hg
  unfold Up
  rwa [Matrix.coe_units_inv]

private theorem Jc (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem ltd_theta_apply (g : GL (Fin 3) R) (a b : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) a b = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val, Jc]

private theorem Up.theta {g : GL (Fin 3) R} (hg : Up g) : Up (theta g) := by
  intro a b h
  rw [ltd_theta_apply]
  exact hg.inv (Fin.rev_lt_rev.mpr h)

private theorem Up.sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) : Up (sgnAct 3 R s g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rwa [sgnAct_one]
  · rw [sgnAct_neg_one]; exact hg.theta

private theorem Up.diag_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) (a : Fin 3) :
    ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a =
      (g : Matrix (Fin 3) (Fin 3) R) a a * (h : Matrix (Fin 3) (Fin 3) R) a a := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h1 | h1
    · rw [hg (show id b < id a from h1), zero_mul]
    · rw [hh (show id a < id b from h1), mul_zero]
  · simp

private def dgl (g : GL (Fin 3) R) (hg : Up g) : GL (Fin 3) R where
  val := Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a
  inv := Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.diag_mul hg.inv, mul_inv_cancel]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.inv.diag_mul hg, inv_mul_cancel]
    simp

private theorem dgl_val (g : GL (Fin 3) R) (hg : Up g) : (dgl g hg : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_inv_val (g : GL (Fin 3) R) (hg : Up g) :
    (((dgl g hg)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) :
    dgl (g * h) (hg.mul hh) = dgl g hg * dgl h hh := by
  apply Units.ext
  rw [Units.val_mul (dgl g hg), dgl_val, dgl_val, dgl_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact hg.diag_mul hh a

private theorem dgl_sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) :
    dgl (sgnAct 3 R s g) (hg.sgn s) = sgnAct 3 R s (dgl g hg) := by
  apply Units.ext
  rw [dgl_val]
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one, dgl_val]
  · rw [sgnAct_neg_one, sgnAct_neg_one]
    ext a b
    rw [ltd_theta_apply, dgl_inv_val]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ltd_theta_apply]
    · rw [Matrix.diagonal_apply_ne _ hab,
        Matrix.diagonal_apply_ne _ (fun h => hab (Fin.rev_injective h).symm)]

private def Bor (R : Type) [CommRing R] : Subgroup (GG (m := 3) (R := R)) where
  carrier := {x | Up x.left}
  mul_mem' := fun {x y} hx hy => by
    change Up (x * y).left
    rw [SemidirectProduct.mul_left]
    exact Up.mul hx (Up.sgn hy _)
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    change Up (x⁻¹).left
    rw [SemidirectProduct.inv_left]
    exact Up.sgn (Up.inv hx) _

private def dgHom (R : Type) [CommRing R] : Bor R →* GG (m := 3) (R := R) :=
  MonoidHom.mk' (fun x => ⟨dgl x.1.left x.2, x.1.right⟩) (fun x y => by
    ext1
    · rw [SemidirectProduct.mul_left]
      change dgl (x.1.left * sgnAct 3 R x.1.right y.1.left) (Up.mul x.2 (Up.sgn y.2 _)) =
        dgl x.1.left x.2 * sgnAct 3 R x.1.right (dgl y.1.left y.2)
      exact (dgl_mul (g := x.1.left) x.2 (Up.sgn (g := y.1.left) y.2 _)).trans
        (congrArg (dgl x.1.left x.2 * ·) (dgl_sgn (g := y.1.left) y.2 _))
    · rfl)

end SlopeTestRemainingChoices

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_diag :
    ∀ {R : Type} [CommRing R] [Finite R],
      ∃ (B : Subgroup (GG (m := 3) (R := R))) (dg : B →* GG (m := 3) (R := R)),
        (∀ x : GG (m := 3) (R := R), x ∈ B ↔ ∀ a b, wt a b < 0 → x.mat a b = 0) ∧
        ∀ x : B, (dg x).right = (x : GG (m := 3) (R := R)).right ∧
          (dg x).mat = Matrix.diagonal fun a => (x : GG (m := 3) (R := R)).mat a a := by
  intro R _ _
  refine ⟨Bor R, dgHom R, fun x => ?_, fun x => ⟨rfl, rfl⟩⟩
  exact ⟨fun h a b hab => h ((ltd_wt_neg_iff a b).1 hab), fun h a b hab => h a b ((ltd_wt_neg_iff a b).2 hab)⟩
end

