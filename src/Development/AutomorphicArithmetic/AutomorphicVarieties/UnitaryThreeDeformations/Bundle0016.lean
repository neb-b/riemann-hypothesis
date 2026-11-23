module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDesc
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private def dualIncl (K : IntermediateField F E) : DualNumber ↥K →+* DualNumber E where
  toFun x := TrivSqZeroExt.inl ((x.fst : ↥K) : E) + TrivSqZeroExt.inr ((x.snd : ↥K) : E)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem dualIncl_fst (K : IntermediateField F E) (x : DualNumber ↥K) :
    (dualIncl K x).fst = ((x.fst : ↥K) : E) := by simp [dualIncl]

private theorem dualIncl_snd (K : IntermediateField F E) (x : DualNumber ↥K) :
    (dualIncl K x).snd = ((x.snd : ↥K) : E) := by simp [dualIncl]

private theorem dualIncl_inj (K : IntermediateField F E) : Function.Injective (dualIncl K) := by
  intro x y h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [dualIncl_fst, dualIncl_fst] at h1
  rw [dualIncl_snd, dualIncl_snd] at h2
  exact TrivSqZeroExt.ext (Subtype.ext h1) (Subtype.ext h2)

private theorem gl_desc (K : IntermediateField F E) (u : GL (Fin 3) (DualNumber E))
    (hu : ∀ a b, ((u : Matrix (Fin 3) (Fin 3) (DualNumber E)) a b).fst ∈ K ∧
      ((u : Matrix (Fin 3) (Fin 3) (DualNumber E)) a b).snd ∈ K) :
    ∃ v : GL (Fin 3) (DualNumber ↥K), Matrix.GeneralLinearGroup.map (dualIncl K) v = u := by
  let A : Matrix (Fin 3) (Fin 3) (DualNumber ↥K) := Matrix.of fun a b =>
    TrivSqZeroExt.inl (⟨_, (hu a b).1⟩ : ↥K) + TrivSqZeroExt.inr (⟨_, (hu a b).2⟩ : ↥K)
  have hA : A.map (dualIncl K) = (u : Matrix (Fin 3) (Fin 3) (DualNumber E)) := by
    refine Matrix.ext fun a b => ?_
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [Matrix.map_apply, dualIncl_fst]; simp [A]
    · rw [Matrix.map_apply, dualIncl_snd]; simp [A]
  have hd : IsUnit A.det := by
    have h1 : IsUnit (dualIncl K A.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hA]
      exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualIncl_fst, isUnit_iff_ne_zero] at h1
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
    intro h0
    exact h1 (by rw [h0]; rfl)
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, Units.ext hA⟩

private theorem gg_range_iff (K : IntermediateField F E) (x : GG (m := 3) (R := DualNumber E)) :
    x ∈ (GG.map (m := 3) (dualIncl K)).range ↔
      ∀ a b, (x.mat a b).fst ∈ K ∧ (x.mat a b).snd ∈ K := by
  constructor
  · rintro ⟨y, rfl⟩ a b
    rw [GG.map_mat, Matrix.map_apply, dualIncl_fst, dualIncl_snd]
    exact ⟨SetLike.coe_mem _, SetLike.coe_mem _⟩
  · intro h
    obtain ⟨v, hv⟩ := gl_desc K x.left h
    exact ⟨⟨v, x.right⟩, SemidirectProduct.ext hv rfl⟩

private theorem ggmap_inj {C B : Type} [CommRing C] [CommRing B] (ι : C →+* B) (hι : Function.Injective ι) :
    Function.Injective (GG.map (m := 3) ι) := fun x y h => by
  refine SemidirectProduct.ext (Units.ext ?_) (congrArg SemidirectProduct.right h :)
  refine Matrix.ext fun a b => ?_
  exact hι (congrFun (congrFun (congrArg GG.mat h) a) b)

private def ents (A : Matrix (Fin 3) (Fin 3) (DualNumber E)) : Set E :=
  Set.range (fun p : Fin 3 × Fin 3 => (A p.1 p.2).fst) ∪
    Set.range (fun p : Fin 3 × Fin 3 => (A p.1 p.2).snd)

private theorem ents_finite (A : Matrix (Fin 3) (Fin 3) (DualNumber E)) : (ents A).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

private theorem of_ents {A : Matrix (Fin 3) (Fin 3) (DualNumber E)} {K : IntermediateField F E}
    (h : ents A ⊆ K) (a b : Fin 3) : (A a b).fst ∈ K ∧ (A a b).snd ∈ K :=
  ⟨h (Or.inl ⟨(a, b), rfl⟩), h (Or.inr ⟨(a, b), rfl⟩)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.rig_desc :
    ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
      [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
      (r' : Γ →* GG (m := 3) (R := DualNumber (PadicAlgCl l)))
      (h : GL (Fin 3) (DualNumber (PadicAlgCl l))),
      (∀ a b, Continuous fun g => ((r' g).mat a b).fst) →
      (∀ a b, Continuous fun g => ((r' g).mat a b).snd) →
      ∃ (L : Formalism.BasicNotions.Loc.FinExt l) (f : DualNumber ↥L.1 →+* DualNumber (PadicAlgCl l))
        (r₁ : Γ →* GG (m := 3) (R := DualNumber ↥L.1)) (h₁ : GL (Fin 3) (DualNumber ↥L.1)),
        (∀ x, (f x).fst = ((x.fst : ↥L.1) : PadicAlgCl l) ∧ (f x).snd = ((x.snd : ↥L.1) : PadicAlgCl l)) ∧
        (GG.map f).comp r₁ = r' ∧ Matrix.GeneralLinearGroup.map f h₁ = h := by
  intro l _ Γ _ _ _ _ _ r' h hc1 hc2
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  let S : IntermediateField ℚ_[l] (PadicAlgCl l) → Subgroup Γ := fun M =>
    (GG.map (m := 3) (dualIncl M)).range.comap r'
  have hS : ∀ M g, g ∈ S M ↔ ∀ a b, ((r' g).mat a b).fst ∈ M ∧ ((r' g).mat a b).snd ∈ M :=
    fun M g => gg_range_iff M (r' g)
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (S (K m) : Set Γ) := fun m => by
    have : (S (K m) : Set Γ) = ⋂ a, ⋂ b,
        ((fun g => ((r' g).mat a b).fst) ⁻¹' (K m) ∩ (fun g => ((r' g).mat a b).snd) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      exact hS _ g
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      ((hKcl m).preimage (hc1 a b)).inter ((hKcl m).preimage (hc2 a b))
  have hun : ⋃ m, (S (K m) : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov _ (ents_finite (r' g).mat)
    exact Set.mem_iUnion.2 ⟨m, (hS _ g).2 (of_ents hm)⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (S (K m) : Set Γ) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ S (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  obtain ⟨n, hn⟩ := hcov (ents (h : Matrix (Fin 3) (Fin 3) (DualNumber (PadicAlgCl l))) ∪
      ⋃ q : Γ ⧸ S (K m), ents (r' q.out).mat)
    ((ents_finite _).union (Set.finite_iUnion fun q => ents_finite _))
  haveI := hK m
  haveI := hK n
  have hmono : ∀ M M', M ≤ M' → S M ≤ S M' := fun M M' hM g hg =>
    (hS _ g).2 fun a b => ⟨hM ((hS _ g).1 hg a b).1, hM ((hS _ g).1 hg a b).2⟩
  have hall : ∀ g, g ∈ S (K n ⊔ K m) := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (S (K m)) g
    have hg : g = (g : Γ ⧸ S (K m)).out * (k : Γ)⁻¹ := by
      rw [hk, mul_inv_cancel_right]
    rw [hg]
    refine mul_mem (hmono _ _ le_sup_left ?_) (hmono _ _ le_sup_right (inv_mem k.2))
    exact (hS _ _).2 (of_ents fun z hz => hn (Or.inr (Set.mem_iUnion.2 ⟨_, hz⟩)))
  obtain ⟨h₁, hh₁⟩ := gl_desc (K n ⊔ K m) h
    (of_ents fun z hz => (le_sup_left : K n ≤ K n ⊔ K m) (hn (Or.inl hz)))
  have hall' : ∀ g, ∃ y, GG.map (m := 3) (dualIncl (K n ⊔ K m)) y = r' g := hall
  choose u hu using hall'
  exact ⟨⟨K n ⊔ K m, inferInstance⟩, dualIncl (K n ⊔ K m),
    MonoidHom.mk' u fun g g' => ggmap_inj _ (dualIncl_inj _) (by rw [map_mul, hu, hu, hu, map_mul]),
    h₁, fun x => ⟨dualIncl_fst _ x, dualIncl_snd _ x⟩, MonoidHom.ext hu, hh₁⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDiag
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rigDiag_fst_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem rigDiag_snd_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib]

private theorem rigDiag_conj_mat {R D : Type} [CommRing R] [Group D] (h : GL (Fin 3) R)
    (r : D →* GG (m := 3) (R := R)) (s : D)
    (hs : (r s).right = 1) :
    (h : Matrix (Fin 3) (Fin 3) R) * (conjBy h⁻¹ r s).mat = (r s).mat * h := by
  simp [conjBy, GG.mat, GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hs]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units h), Matrix.one_mul]

theorem UpperTheory.V.UnitaryThreeInertia.rig_diag :
    ∀ {O K D : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := K))
      (y : D → Matrix (Fin 3) (Fin 3) K) (r' : D →* GG (m := 3) (R := DualNumber K))
      (h : GL (Fin 3) (DualNumber K)),
      (∀ s ∈ I, η s = 1) → HasMult η r →
      IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
        (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' →
      DiagIn η Ψ I r' h → ∃ X, ∀ s ∈ I, y s = adRep r s X - X := by
  intro O K D _ _ _ _ _ η Ψ I r y r' h hI hm hd hD
  set H : Matrix (Fin 3) (Fin 3) (DualNumber K) := (h : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hH
  set Hi : Matrix (Fin 3) (Fin 3) (DualNumber K) := (↑h⁻¹ : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hHi
  refine ⟨-(H.map TrivSqZeroExt.snd * Hi.map TrivSqZeroExt.fst), fun s hs => ?_⟩
  have hη : η s = 1 := hI s hs
  have hr1 : (r s).right = 1 := (hm s).trans hη
  have hd1 := hd s
  have hr'1 : (r' s).right = 1 := by
    rw [hd1.1]
    simpa [GG.map] using hr1
  have hmat : (r' s).mat = (1 + (y s).map TrivSqZeroExt.inr) * (r s).mat.map (algebraMap K (DualNumber K)) := by
    rw [hd1.2]
    simp [GG.map, GG.mat]
  have hker : s ∈ η.ker := hη
  have hoff : ∀ a b, ((conjBy h⁻¹ r' s).mat a b).snd = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hD.ine s hs hη a]
      rfl
    · rcases lt_or_gt_of_ne (show wt a b ≠ 0 by revert a b; decide) with hlt | hlt
      · rw [hD.tri s hker a b hlt]
        rfl
      · rw [hD.low s hker a b hlt]
        rfl
  set C := (conjBy h⁻¹ r' s).mat with hC
  set R := (r s).mat with hR
  set h0 := H.map TrivSqZeroExt.fst
  set h1 := H.map TrivSqZeroExt.snd
  set g0 := Hi.map TrivSqZeroExt.fst
  set C0 := C.map TrivSqZeroExt.fst
  have hc : H * C = (r' s).mat * H := rigDiag_conj_mat h r' s hr'1
  have hCs : C.map TrivSqZeroExt.snd = 0 := by
    ext a b
    exact hoff a b
  have hM0 : (r' s).mat.map TrivSqZeroExt.fst = R := by
    rw [hmat, rigDiag_fst_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, ite_mul]
  have hM1 : (r' s).mat.map TrivSqZeroExt.snd = y s * R := by
    rw [hmat, rigDiag_snd_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl,
      apply_ite TrivSqZeroExt.fst, apply_ite TrivSqZeroExt.snd]
  have e0 : h0 * C0 = R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hc
    simpa only [rigDiag_fst_mul, hM0] using this
  have e1 : h1 * C0 = R * h1 + y s * R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.snd) hc
    simp only [rigDiag_snd_mul, hM0, hM1, hCs, Matrix.mul_zero, zero_add] at this
    exact this
  have hinv1 : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv2 : H * Hi = 1 := by
    rw [hHi, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgh : g0 * h0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv1
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hhg : h0 * g0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv2
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hRR : R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hR, GG.mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : C0 = g0 * R * h0 := by
    rw [← one_mul C0, ← hgh, mul_assoc, e0, ← mul_assoc]
  have e3 : y s * R = h1 * g0 * R - R * (h1 * g0) := by
    have k : y s * R * h0 = h1 * C0 - R * h1 := by
      rw [e1]
      abel
    calc y s * R = y s * R * h0 * g0 := by rw [mul_assoc (y s * R), hhg, mul_one]
      _ = (h1 * C0 - R * h1) * g0 := by rw [k]
      _ = h1 * g0 * R - R * (h1 * g0) := by
        rw [e2]
        simp only [sub_mul, mul_assoc, hhg, mul_one]
  have e4 : y s = y s * R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_assoc, hRR, mul_one]
  rw [e4, e3]
  simp only [adRep, GG.ad, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, GG.adFun, hr1, ite_true]
  rw [← hR]
  simp only [sub_mul, mul_assoc, hRR, mul_one, mul_neg, neg_mul, sub_neg_eq_add]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSep
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (a : n) (h1 : ∀ i j, ‖A i j‖ ≤ 1) (h2 : ∀ j, ‖A a j‖ < 1) :
    ‖A.det‖ < 1 := by
  rw [Matrix.det_apply']
  obtain ⟨σ, -, hσ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty (α := Equiv.Perm n))
    (fun τ : Equiv.Perm n => (((Equiv.Perm.sign τ : ℤ) : K)) * ∏ i, A (τ i) i)
  refine lt_of_le_of_lt hσ ?_
  show ‖(((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, A (σ i) i‖ < 1
  have hs : ‖(((Equiv.Perm.sign σ : ℤ) : K))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, one_mul, norm_prod,
    ← Finset.mul_prod_erase Finset.univ (fun i => ‖A (σ i) i‖) (Finset.mem_univ (σ.symm a))]
  have hle : ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => h1 _ _)
  have hlt : ‖A (σ (σ.symm a)) (σ.symm a)‖ < 1 := by
    rw [Equiv.apply_symm_apply]
    exact h2 _
  calc ‖A (σ (σ.symm a)) (σ.symm a)‖ * ∏ i ∈ Finset.univ.erase (σ.symm a), ‖A (σ i) i‖
      ≤ ‖A (σ (σ.symm a)) (σ.symm a)‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ < 1 := by simpa using hlt

private theorem norm_le_one_of_det_smul_one_sub_eq_zero {K : Type*} [NormedField K] [IsUltrametricDist K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h1 : ∀ i j, ‖M i j‖ ≤ 1) (t : K)
    (ht : (t • (1 : Matrix n n K) - M).det = 0) : ‖t‖ ≤ 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
  rcases isEmpty_or_nonempty n with hn | hn
  · exact absurd (funext fun c => (IsEmpty.false c).elim) hv0
  obtain ⟨b, hb⟩ := Finite.exists_max (fun c => ‖v c‖)
  have hvb : v b ≠ 0 := by
    intro h0
    apply hv0
    funext c
    have := hb c
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow : t * v b = ∑ c, M b c * v c := by
    have := congrFun hv b
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq] at this
    linear_combination this
  have hbound : ‖t * v b‖ ≤ 1 * ‖v b‖ := by
    rw [hrow]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) (fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (h1 b c) (hb c) (norm_nonneg _) zero_le_one
  rw [norm_mul] at hbound
  exact le_of_mul_le_mul_right hbound (norm_pos_iff.mpr hvb)

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.UnitaryThreeInertia.rig_sep :
    ∀ {l : ℕ} [Fact l.Prime] (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) (d : Fin 3 → PadicAlgCl l) (P : GL (Fin 3) (PadicAlgCl l)), (∀ a b, ‖M a b - Matrix.diagonal d a b‖ < 1) → (∀ a, ‖d a‖ = 1) → (∀ a b, a ≠ b → ‖d a - d b‖ = 1) → (∀ i j, j < i → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i j = 0) → ∀ i j, i ≠ j → ∀ u : PadicAlgCl l, ‖u - 1‖ < 1 → (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) i i ≠ (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))) j j * u := by
  intro l _ M d P hM hd hdd hT i j hij u hu
  set T := ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * M *
    (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) with hTdef
  have hsub : ∀ x y : PadicAlgCl l, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hdet : ∀ x : PadicAlgCl l, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det =
      ∏ k, (x - T k k) := by
    intro x
    have h1 : ((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
        (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) = x • 1 - T := by
      rw [hTdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Units.inv_mul]
    have h2 : (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
        ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have h3 : (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T).det =
        ∏ k, (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - T) k k := by
      apply Matrix.det_of_upperTriangular
      intro a b hab
      have hne : a ≠ b := (ne_of_lt hab).symm
      simp [Matrix.sub_apply, Matrix.one_apply, hne, hT a b hab]
    calc (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det
        = ((((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det *
          ((P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det) *
          (x • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det := by rw [h2, one_mul]
      _ = (((P⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) *
          (x • 1 - M) * (P : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).det := by
        rw [Matrix.det_mul, Matrix.det_mul]
        ring
      _ = ∏ k, (x - T k k) := by
        rw [h1, h3]
        simp [Matrix.sub_apply, Matrix.one_apply]
  have hM1 : ∀ a b, ‖M a b‖ ≤ 1 := by
    intro a b
    have hdg : ‖Matrix.diagonal d a b‖ ≤ 1 := by
      by_cases hab : a = b
      · subst hab
        simp [hd a]
      · simp [Matrix.diagonal_apply_ne _ hab]
    have := IsUltrametricDist.norm_add_le_max (M a b - Matrix.diagonal d a b) (Matrix.diagonal d a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM a b).le hdg)
  have ht1 : ∀ k, ‖T k k‖ ≤ 1 := fun k =>
    norm_le_one_of_det_smul_one_sub_eq_zero M hM1 (T k k) (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _))
  have ht2 : ∀ a, ∃ k, ‖d a - T k k‖ < 1 := by
    intro a
    have hsmall : ‖(d a • (1 : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) - M).det‖ < 1 := by
      apply norm_det_lt_one_of_norm_le_one_of_norm_apply_lt_one _ a
      · intro c b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        refine (hsub _ _).trans (max_le ?_ (hM1 c b))
        by_cases hcb : c = b
        · subst hcb
          simp [Matrix.one_apply_eq, hd a]
        · simp [Matrix.one_apply_ne hcb]
      · intro b
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        by_cases hab : a = b
        · subst hab
          have := hM a a
          rw [Matrix.diagonal_apply_eq] at this
          rw [norm_sub_rev] at this
          simpa using this
        · have := hM a b
          rw [Matrix.diagonal_apply_ne _ hab, sub_zero] at this
          simpa [Matrix.one_apply_ne hab] using this
    rw [hdet, norm_prod, Fin.prod_univ_three] at hsmall
    by_contra hne
    push_neg at hne
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hne 0) (hne 1)) (hne 2)
    linarith
  choose φ hφ using ht2
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h := hdd a b hne
    have : ‖d a - d b‖ ≤ max ‖d a - T (φ a) (φ a)‖ ‖d b - T (φ a) (φ a)‖ := by
      have := hsub (d a - T (φ a) (φ a)) (d b - T (φ a) (φ a))
      simpa using this
    rw [hab] at this
    have := this.trans_lt (max_lt (hab ▸ hφ a) (hφ b))
    linarith
  have hsurj := Finite.surjective_of_injective hinj
  obtain ⟨a, rfl⟩ := hsurj i
  obtain ⟨b, rfl⟩ := hsurj j
  have hab : a ≠ b := fun h => hij (h ▸ rfl)
  intro heq
  have hclose : ‖T (φ a) (φ a) - T (φ b) (φ b)‖ < 1 := by
    rw [heq, show T (φ b) (φ b) * u - T (φ b) (φ b) = T (φ b) (φ b) * (u - 1) by ring, norm_mul]
    calc ‖T (φ b) (φ b)‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (ht1 _) (norm_nonneg _)
      _ < 1 := by linarith
  have hsplit : d a - d b = (d a - T (φ a) (φ a)) +
      ((T (φ a) (φ a) - T (φ b) (φ b)) + (T (φ b) (φ b) - d b)) := by ring
  have h3 : ‖d a - d b‖ < 1 := by
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ a) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hclose ?_)
    rw [norm_sub_rev]
    exact hφ b
  have := hdd a b hab
  linarith
end

