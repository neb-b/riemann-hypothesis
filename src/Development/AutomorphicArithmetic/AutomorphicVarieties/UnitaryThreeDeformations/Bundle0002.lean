module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  rfl

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    map_mul, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R))
    (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]; rfl

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨htri, hine⟩ := H
  refine ⟨?_, ?_⟩
  · unfold Upper at htri ⊢
    intro g hg a b hab
    rw [conj_push_mat, htri g hg a b hab, map_zero]
  · intro s hs hη a
    rw [conj_push_mat, hine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG (m := 3) (R := R)} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) := by
  obtain ⟨H1, hlow⟩ := H
  refine ⟨triIn_push φ H1, ?_⟩
  unfold Lower at hlow ⊢
  intro g hg a b hab
  rw [conj_push_mat, hlow g hg a b hab, map_zero]

variable [IsLocalRing R] [IsLocalRing R']

private theorem map_mem_max (φ : R →ₐ[O] R') [IsLocalHom φ] {x : R} (hx : x ∈ maximalIdeal R) :
    φ x ∈ maximalIdeal R' := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun hu => hx (isUnit_of_map_unit φ x hu)

private theorem inHat_push (φ : R →ₐ[O] R') [IsLocalHom φ] {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  unfold InHat CongOne EntIn at *
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  exact map_mem_max φ (H a b)

private theorem adicCont_push [TopologicalSpace D] (φ : R →ₐ[O] R') [IsLocalHom φ]
    {r : D →* GG (m := 3) (R := R)}
    (H : AdicCont (maximalIdeal R) r) : AdicCont (maximalIdeal R') (push φ r) := by
  unfold UpperTheory.V.UnitaryThreeInertia.AdicCont at *
  intro n
  have hle : ∀ x ∈ maximalIdeal R ^ n, (φ : R →+* R') x ∈ maximalIdeal R' ^ n := by
    intro x hx
    have h1 : Ideal.map (φ : R →+* R') (maximalIdeal R) ≤ maximalIdeal R' := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact map_mem_max φ hy
    have h2 : Ideal.map (φ : R →+* R') (maximalIdeal R ^ n) ≤ maximalIdeal R' ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono h1 n
    exact h2 (Ideal.mem_map_of_mem _ hx)
  let ψ : R ⧸ maximalIdeal R ^ n →+* R' ⧸ maximalIdeal R' ^ n :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : R →+* R'))
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hle x hx))
  have hfun : (fun g => ((push φ r) g).mat.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) =
      (fun M => M.map ψ) ∘ (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal R ^ n))) := by
    funext g
    ext a b
    simp only [Function.comp_apply, Matrix.map_apply, ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  rw [hfun]
  exact (H n).comp _

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.isPt_push :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ]
      (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
      [CommRing R'] [IsLocalRing R'] [Algebra O R'] (φ : R →ₐ[O] R') [IsLocalHom φ] (g₁ : Γ)
      (r : Γ →* GG (m := 3) (R := R)), F.IsPt g₁ r → F.IsPt g₁ (push φ r) := by
  intro O _ _ G Γ ι _ _ _ F R R' _ _ _ _ _ _ φ _ g₁ r hr
  have hmat : ∀ x : GG (m := 3) (R := R), ((GG.map (φ : R →+* R')) x).mat = x.mat.map φ := fun x => rfl
  have hpm : ∀ g, ((push φ r) g).mat = (r g).mat.map φ := fun g => hmat (r g)
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, adicCont_push φ hr.cont⟩
  · have hm := hr.mult
    unfold HasMult at hm ⊢
    intro g
    exact hm g
  · intro g a b
    rw [Matrix.sub_apply, hpm, Matrix.map_apply, Matrix.map_apply, ← AlgHom.commutes φ, ← map_sub]
    apply map_mem_max φ
    have := hr.red g a b
    rwa [Matrix.sub_apply, Matrix.map_apply] at this
  · intro v
    have hv := hr.loc v
    unfold Frame.LocAt at hv ⊢
    obtain ⟨hT, hD, hU⟩ := hv
    unfold CondT CondD CondU at *
    have hcomp : (push φ r).comp (F.loc v) = push φ (r.comp (F.loc v)) := rfl
    rw [hcomp]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk, htr⟩ := hT h
      exact ⟨_, inHat_push φ hk, triIn_push φ htr⟩
    · obtain ⟨k, hk, hdi⟩ := hD h
      exact ⟨_, inHat_push φ hk, diagIn_push φ hdi⟩
    · intro s hs
      show (GG.map (φ : R →+* R')) ((r.comp (F.loc v)) s) = 1
      rw [hU h s hs, map_one]
  · obtain ⟨hatc, hz12, hz21⟩ := hr.norm
    refine ⟨?_, ?_, ?_⟩
    · rw [hpm, hatc, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · unfold zmat at hz12 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz12,
        map_zero]
    · unfold zmat at hz21 ⊢
      rw [Matrix.sub_apply, hpm, hpm, Matrix.map_apply, Matrix.map_apply, ← map_sub, ← Matrix.sub_apply, hz21,
        map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUniqueIsPtHom
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem gg_ext {R : Type} [CommRing R] {x y : GG (m := 3) (R := R)} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG (m := 3) (R := R)) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart (O := O) u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl (R := R') 3) * GeneralLinearGroup.det (Jgl (R := R') 3) = 1 := by
      rw [← map_mul, Jgl_mul_Jgl, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG (m := 3) (R := R)) (ξ : Sring (O := O) u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring (O := O) u := fun g a b =>
    mem_Sring u (entry_mem u g a b)
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring (O := O) u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring (O := O) u :=
      mem_Sring u hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring (O := O) u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring (O := O) u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring (O := O) u).val : Sring (O := O) u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring (O := O) u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring (O := O) u).val : Sring (O := O) u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG (m := 3) (R := Sring (O := O) u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring (O := O) u).val : Sring (O := O) u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG (m := 3) (R := Sring (O := O) u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring (O := O) u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsWeightedEquationsPresentingKer
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul {O σ : Type} [CommRing O] (i : σ) (a g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    coeff (Finsupp.single i 1) (a * g) = constantCoeff a * coeff (Finsupp.single i 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, hg]

private noncomputable def pad {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n) : FA O wt :=
  if h : k.val < b then mkF (f ⟨k.val, h⟩) (hf _) else 0

private theorem pad_ind {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n)
    (P : FA O wt → Prop) (h0 : P 0) (h1 : ∀ i, P (mkF (f i) (hf i))) : P (pad f hf n k) := by
  unfold pad
  split_ifs
  · exact h1 _
  · exact h0

private theorem pad_range {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) {n : ℕ} (h : b ≤ n) (i : Fin b) :
    mkF (f i) (hf i) ∈ Set.range (pad f hf n) :=
  ⟨⟨i.val, lt_of_lt_of_le i.2 h⟩, by simp [pad]⟩

private theorem der_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ho : W.HasOrigin)
    (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O) (hf : ∀ j i, f j i ∈ wtPart O W.wt j)
    (hk : RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j))) (j0 : ℤ) (n : ℕ) (hn : b j0 ≤ n)
    (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N) (hd : ∀ i, W.wt i ≠ j0 → d i = 0)
    (hF : ∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (pad (f j0) (hf j0) n k)) • d i = 0)
    (g : MvPowerSeries W.σ O) (hg : W.π g = 0) : ∑ i, coeff (Finsupp.single i 1) g • d i = 0 := by
  have hg' : g ∈ Ideal.span (⋃ j, Set.range (f j)) := hk ▸ hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hx
    by_cases hj : j = j0
    · subst hj
      obtain ⟨k, e⟩ := pad_range (f j) (hf j) hn i
      have := hF k
      rwa [e] at this
    · refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : W.wt v = j0
      · rw [hf j i _ (by simpa [Finsupp.weight_single, hv] using Ne.symm hj), zero_smul]
      · rw [hd v hv, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x hx ih =>
    have h0 : constantCoeff x = 0 := ho x (hk.ge hx)
    simp only [smul_eq_mul, coeff_single_mul _ a x h0, mul_smul, ← Finset.smul_sum, ih, smul_zero]

theorem UpperTheory.exists_weighted_equations_presenting_ker :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R), W.HasOrigin →
        ∀ (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O), (∀ j i, f j i ∈ wtPart O W.wt j) →
        RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)) → ∀ r s r' s' m : ℕ,
        b (-1) ≤ r + 1 → b (-2) ≤ s → b 1 ≤ r' → b 2 ≤ s' → b 0 ≤ m → (∀ j, j < -2 ∨ 2 < j → b j = 0) →
        ∃ Q : Eqns (Fgr O W.wt) (x0 O W.wt) r s r' s' m, Q.ideal = RingHom.ker (toA W) ∧
          ∀ (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N),
            (((∀ i, W.wt i ≠ -1 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.F k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ -2 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.G k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ 0 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.Z k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0)) := by
  intro O R _ _ _ W ho b f hf hk r s r' s' m h1 h2 h3 h4 h5 h6
  have hker : ∀ j i, W.π (f j i) = 0 := fun j i => by
    have : f j i ∈ RingHom.ker W.π := hk ▸ Ideal.subset_span (Set.mem_iUnion.2 ⟨j, i, rfl⟩)
    exact this
  have hmem : ∀ j n k, pad (f j) (hf j) n k ∈ Fgr O W.wt j := fun j n k =>
    pad_ind _ _ n k (· ∈ Fgr O W.wt j) (zero_mem _) fun i => mkF_mem _ _
  have hkA : ∀ j n, Set.range (pad (f j) (hf j) n) ⊆ RingHom.ker (toA W) := by
    rintro j n _ ⟨k, rfl⟩
    exact pad_ind _ _ n k (· ∈ RingHom.ker (toA W)) (zero_mem _) fun i => Subtype.ext (hker j i)
  refine ⟨⟨pad (f (-1)) (hf _) _, pad (f (-2)) (hf _) _, pad (f 1) (hf _) _, pad (f 2) (hf _) _,
    pad (f 0) (hf _) _, hmem _ _, hmem _ _, hmem _ _, hmem _ _, fun k => ⟨hmem _ _ _, ?_⟩⟩, ?_,
    fun N _ _ d => ⟨der_zero W ho b f hf hk _ _ h1 N d, der_zero W ho b f hf hk _ _ h2 N d,
      der_zero W ho b f hf hk _ _ h5 N d⟩⟩
  · exact pad_ind _ _ m k (fun y => x0 O W.wt y = 0) (map_zero _) fun i => by
      rw [weightedSeriesOrigin_apply]; exact ho _ (hker 0 i)
  · refine le_antisymm (Ideal.span_le.2 ?_) fun x hx => ?_
    · simp only [Set.union_subset_iff]
      exact ⟨⟨⟨⟨hkA _ _, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩
    · have hx1 : ser x ∈ RingHom.ker W.π := congrArg Subtype.val (show toA W x = 0 from hx)
      rw [hk] at hx1
      have H := (homog_span O _ ℤ (WPres.free O W.wt) (Σ j : Finset.Icc (-2 : ℤ) 2, Fin (b j))
        (fun p => mkF (f p.1 p.2) (hf _ _)) (fun p => p.1) (fun p => mkF_mem _ _)).2 x
      refine Ideal.span_mono ?_ (H.1 (Ideal.span_mono ?_ hx1))
      · rintro _ ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
        have hj' := Finset.mem_Icc.1 hj
        have : j = -1 ∨ j = -2 ∨ j = 1 ∨ j = 2 ∨ j = 0 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (pad_range _ _ h1 i))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (pad_range _ _ h2 i))))
        · exact Or.inl (Or.inl (Or.inr (pad_range _ _ h3 i)))
        · exact Or.inl (Or.inr (pad_range _ _ h4 i))
        · exact Or.inr (pad_range _ _ h5 i)
      · intro y hy
        obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hy
        have hj : j ∈ Finset.Icc (-2 : ℤ) 2 := by
          by_contra hc
          have := h6 j (by rw [Finset.mem_Icc] at hc; omega)
          have := i.2
          omega
        exact ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GradedMatrixMulInv
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG (m := 3) (R := R)),
      GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformU
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.locAt_deform_u :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v ∉ F.Tb →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j)
        (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F _ _ R _ _ _ f hf _ j v hv r r₂ z γ _ hr hz hγ hd
  have hvl : v ≠ F.vl := fun h => hv (h ▸ Set.mem_insert _ _)
  refine ⟨fun h => absurd h hvl, fun h => absurd (Set.mem_insert_of_mem _ h) hv, fun _ s hs => ?_⟩
  have h1 : r s = 1 := hr.2.2 hv s hs
  have hz0 : z s = 0 := hz.2.1 hvl s hs
  have hγ0 : γ s = 0 := by
    ext a b
    obtain ⟨o, ho, e⟩ := hγ s a b
    rw [hz0] at ho
    have ho' : o ∈ maximalIdeal O := (residue_eq_zero_iff o).1 ho
    have hm : algebraMap O R o ∈ maximalIdeal R := fun h => ho' (IsLocalHom.map_nonunit o h)
    rw [e, Algebra.smul_def]
    exact hf _ hm
  obtain ⟨e1, e2⟩ := hd s
  rw [h1] at e1
  rw [h1, hγ0, add_zero, one_mul] at e2
  exact SemidirectProduct.ext (Units.ext e2) e1
end

