module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ShiftMap
section
private def UpperTheory.Reformulated.B.ShiftMap.shift {G H : Type} [Group G] [Group H] (p : G →* H) :
    G →* ((H → ℂ) →ₗ[ℂ] (H → ℂ)) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun z => (p g)⁻¹ * z)
  map_one' := by
    ext φ z
    simp [LinearMap.funLeft]
  map_mul' g h := by
    ext φ z
    simp [LinearMap.funLeft, mul_assoc]

private lemma UpperTheory.Reformulated.B.ShiftMap.shift_apply {G H : Type} [Group G] [Group H] (p : G →* H)
    (g : G) (φ : H → ℂ) (z : H) : UpperTheory.Reformulated.B.ShiftMap.shift p g φ z = φ ((p g)⁻¹ * z) := rfl

theorem UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : Group H] [inst_4 : TopologicalSpace H] [IsTopologicalGroup H] (p : G →* H),
    Continuous (⇑p : G → H) →
      ∀ (f : H → ℂ),
        Continuous f →
          FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f (((p : G → H) k)⁻¹ * z))) →
            ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ),
              Continuous (⇑ρ : G → Matrix (Fin d) (Fin d) ℂ) ∧
                ∀ (x : G →₀ ℂ),
                  (x.sum fun (k : G) (c : ℂ) ↦ c • (ρ : G → Matrix (Fin d) (Fin d) ℂ) k) =
                      (0 : Matrix (Fin d) (Fin d) ℂ) →
                    ∀ (z : H), (x.sum fun (k : G) (c : ℂ) ↦ c * f (((p : G → H) k)⁻¹ * z)) = (0 : ℂ) := by
  intro G H _ _ _ _ _ _ p hp f hf hfd
  set V : Submodule ℂ (H → ℂ) :=
    Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f ((p k)⁻¹ * z)) with hV
  have hinv : ∀ g : G, ∀ φ ∈ V, UpperTheory.Reformulated.B.ShiftMap.shift p g φ ∈ V := by
    intro g
    have h : V ≤ V.comap (UpperTheory.Reformulated.B.ShiftMap.shift p g) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨g * k, ?_⟩
      funext z
      simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc]
    exact fun φ hφ => h hφ
  have hcont : ∀ φ ∈ V, Continuous φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨k, rfl⟩ := h
      exact hf.comp (continuous_const.mul continuous_id)
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hfV : f ∈ V := Submodule.subset_span ⟨1, by funext z; simp⟩
  let σ : G →* (V →ₗ[ℂ] V) :=
    { toFun := fun g => (UpperTheory.Reformulated.B.ShiftMap.shift p g).restrict (hinv g)
      map_one' := by
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply]
      map_mul' := by
        intro g h
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc] }
  have hσ : ∀ (g : G) (φ : V) (z : H), (σ g φ : H → ℂ) z = (φ : H → ℂ) ((p g)⁻¹ * z) :=
    fun _ _ _ => rfl
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  refine ⟨Module.finrank ℂ V, (e.toAlgHom.toRingHom.toMonoidHom).comp σ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun g : G => σ g (b j) := by
      refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
      exact (hcont _ (b j).2).comp (hp.inv.mul continuous_const)
    have h2 : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    refine (h2.comp h1).congr fun g => ?_
    change _ = LinearMap.toMatrixAlgEquiv b (σ g) i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    rfl
  · intro x hx z
    have h1 : (x.sum fun k c => c • σ k) = 0 := by
      apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, ← hx, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      rfl
    have h2 := congrArg (fun T : V →ₗ[ℂ] V => (T ⟨f, hfV⟩ : H → ℂ) z) h1
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, hσ] using h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignActionTheta
section
noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.SignActionTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.SignActionTheta.Jmat R m * UpperTheory.Reformulated.B.SignActionTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [UpperTheory.Reformulated.B.SignActionTheta.Jmat, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev, Matrix.one_apply]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, inv := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.SignActionTheta.J_mul_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.SignActionTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (g * h) = UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.SignActionTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.SignActionTheta.Jmat]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl <;> rw [h, Fin.rev_rev]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.SignActionTheta.theta (UpperTheory.Reformulated.B.SignActionTheta.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv,
    UpperTheory.Reformulated.B.SignActionTheta.trInv_J]
  simp only [← mul_assoc]
  rw [UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul, mul_assoc, UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, mul_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.SignActionTheta.theta (g * h) = UpperTheory.Reformulated.B.SignActionTheta.theta g * UpperTheory.Reformulated.B.SignActionTheta.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.trInv h * _),
    UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.SignActionTheta.theta, invFun := UpperTheory.Reformulated.B.SignActionTheta.theta, left_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.SignActionTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [if_pos (by simp), if_neg hne]
    ext1 g
    exact (UpperTheory.Reformulated.B.SignActionTheta.aux8 g).symm

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.SignActionTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R] ℤˣ

private theorem UpperTheory.Reformulated.B.SignActionTheta.map_theta {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.theta g) =
      UpperTheory.Reformulated.B.SignActionTheta.theta (Matrix.GeneralLinearGroup.map f g) := by
  have hJ : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl S m := by
    ext i j
    change f (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m i j) = UpperTheory.Reformulated.B.SignActionTheta.Jmat S m i j
    unfold UpperTheory.Reformulated.B.SignActionTheta.Jmat
    split_ifs <;> simp
  have hT : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.trInv g) =
      UpperTheory.Reformulated.B.SignActionTheta.trInv (Matrix.GeneralLinearGroup.map f g) := by
    ext i j
    rfl
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [map_mul, map_mul, hJ, hT]

theorem UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm.{u_1, u_2} :
    ∀ {m : ℕ} {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) (s : ℤˣ),
      (Matrix.GeneralLinearGroup.map f).comp
          (MulEquiv.toMonoidHom ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) s)) =
        (MulEquiv.toMonoidHom
              ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S : ℤˣ → MulAut (GL (Fin m) S)) ((MonoidHom.id ℤˣ : ℤˣ → ℤˣ) s))).comp
          (Matrix.GeneralLinearGroup.map f) := by
  intro m R S _ _ f s
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · ext1 g
    simp
  · have h1 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R :=
      if_neg (t := (1 : MulAut (GL (Fin m) R))) hne
    have h2 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m S :=
      if_neg (t := (1 : MulAut (GL (Fin m) S))) hne
    rw [MonoidHom.id_apply, h1, h2]
    refine MonoidHom.ext fun g => ?_
    exact UpperTheory.Reformulated.B.SignActionTheta.map_theta f g

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.map.{u_1, u_2} :
    {m : ℕ} →
      {R : Type u_1} →
        {S : Type u_2} →
          [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → UpperTheory.Reformulated.B.SignActionTheta.GG m R →* UpperTheory.Reformulated.B.SignActionTheta.GG m S :=
    fun {m : ℕ} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] (f : R →+* S) ↦
      SemidirectProduct.map (Matrix.GeneralLinearGroup.map f) (MonoidHom.id ℤˣ) (UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm f)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) → G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.SignActionTheta.GG m R → MulAut (UpperTheory.Reformulated.B.SignActionTheta.GG m R))
              ((UpperTheory.Reformulated.B.SignActionTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.SignActionTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.SignActionTheta.map_conjBy :
    ∀ {G R S : Type} [inst : Group G] [inst_1 : CommRing R] [inst_2 : CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
      (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R),
      (UpperTheory.Reformulated.B.SignActionTheta.map f).comp (UpperTheory.Reformulated.B.SignActionTheta.conjBy h r) =
        UpperTheory.Reformulated.B.SignActionTheta.conjBy ((Matrix.GeneralLinearGroup.map f : GL (Fin m) R → GL (Fin m) S) h)
          ((UpperTheory.Reformulated.B.SignActionTheta.map f).comp r) := by
  intro G R S _ _ _ m f h r
  refine MonoidHom.ext fun x => ?_
  have hi : UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h) =
      UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) :=
    SemidirectProduct.map_inl _ _ _ h
  change UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h * r x * (UpperTheory.Reformulated.B.SignActionTheta.ofGL h)⁻¹) =
    UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) * UpperTheory.Reformulated.B.SignActionTheta.map f (r x) *
      (UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹
  rw [map_mul, map_mul, map_inv, hi]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemOfDiagonal
section
theorem UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag :
    ∀ {κ : Type} [inst : Field κ] {m : ℕ} (d : Fin m → κ),
    Function.Injective d →
      ∀ (W : Submodule κ (Fin m → κ)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ v ∈ W, ∀ (i : Fin m), v i ≠ (0 : κ) → Pi.single i (1 : κ) ∈ W := by
  intro κ _ m d hd W hW v hv i hi
  have key : ∀ s : Finset (Fin m), (fun k => (∏ j ∈ s, (d k - d j)) * v k) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | insert a s ha ih =>
      have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
      convert h using 1
      funext k
      simp only [Finset.prod_insert ha, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
        smul_eq_mul]
      ring
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (key (Finset.univ.erase i))
  convert h using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hc).symm
  · have h0 : (∏ j ∈ Finset.univ.erase i, (d k - d j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, h0, zero_mul, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemSubmodule
section
theorem UpperTheory.Reformulated.B.SingleMemSubmodule.single_mem :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (W : Submodule K (Fin (3 : ℕ) → K)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ {v : Fin (3 : ℕ) → K}, v ∈ W → ∀ {i : Fin (3 : ℕ)}, v i ≠ (0 : K) → Pi.single i (1 : K) ∈ W := by
  intro K _ d hd W hW v hv i hi
  have step : ∀ (c : K), ∀ w ∈ W, (fun l => (d l - c) * w l) ∈ W := by
    intro c w hw
    have h := W.sub_mem (hW w hw) (W.smul_mem c hw)
    have e : (fun l => (d l - c) * w l) = (Matrix.diagonal d).mulVec w - c • w := by
      funext l
      simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
      ring
    rw [e]
    exact h
  have iter : ∀ s : Finset (Fin 3), (fun l => (∏ j ∈ s, (d l - d j)) * v l) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun l => (∏ j ∈ (∅ : Finset (Fin 3)), (d l - d j)) * v l) = v := by
        funext l
        simp
      rw [e]
      exact hv
    | insert a s ha ih =>
      have h := step (d a) _ ih
      have e : (fun l => (∏ j ∈ insert a s, (d l - d j)) * v l)
          = fun l => (d l - d a) * ((∏ j ∈ s, (d l - d j)) * v l) := by
        funext l
        rw [Finset.prod_insert ha, mul_assoc]
      rw [e]
      exact h
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) hi
    intro j hj
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (iter (Finset.univ.erase i))
  have e : (Pi.single i (1 : K) : Fin 3 → K)
      = ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ •
        (fun l => (∏ j ∈ Finset.univ.erase i, (d l - d j)) * v l) := by
    funext l
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc]
    · have hz : ∏ j ∈ Finset.univ.erase i, (d l - d j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (sub_self _)
      rw [Pi.single_eq_of_ne hl, hz, zero_mul, mul_zero]
  rw [e]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOnAdditive
section
noncomputable def UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn.{u_1, u_3} :
    {E : Type u_1} →
      {V : Type u_3} →
        [inst : NormedAddCommGroup E] →
          [NormedSpace ℝ E] → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → Set E → (E → V) → Prop :=
    fun {E : Type u_1} {V : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
        (A : Set E) (f : E → V) ↦
      ∀ a ∈ A, ∃ (U : Set E) (F : E → V), IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ g ∈ U, g ∈ A → f g = F g

namespace UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

private lemma smOn_zero {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : Set E) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun _ : E => (0 : V)) := by
  intro a _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

private lemma smOn_add {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f g : E → V}
    (hf : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A f) (hg : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A g) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun x => f x + g x) := by
  intro a ha
  obtain ⟨U1, F1, hU1, ha1, hF1, he1⟩ := hf a ha
  obtain ⟨U2, F2, hU2, ha2, hF2, he2⟩ := hg a ha
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨ha1, ha2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), ?_⟩
  intro x hx hxA
  simp only [he1 x hx.1 hxA, he2 x hx.2 hxA]

end UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

open UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers in
theorem UpperTheory.Reformulated.B.SmoothOnAdditive.main.{u_1, u_2, u_3} :
    ∀ {E : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      [inst_2 : NormedAddCommGroup V] [inst_3 : NormedSpace ℝ V] {A : Set E} {f : ι → E → V} (s : Finset ι),
      (∀ i ∈ s, UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (f i)) → UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A fun (a : E) ↦ ∑ i ∈ s, f i a := by
  intro E V ι _ _ _ _ A f s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (smOn_zero (V := V) A)
  | insert j s hj ih =>
    intro h
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := smOn_add h1 h2
    simpa [Finset.sum_insert hj] using this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothQuot
section
namespace UpperTheory.Reformulated.B.Gwb5

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem smooth_quot {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
    [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G U} (h : IsSmooth ρ)
    (T : Submodule ℂ U) (hst : ∀ g : G, T ≤ Submodule.comap (ρ g) T) :
    IsSmooth (ρ.quotient T hst) := by
  intro v
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective T v
  let H : Subgroup G :=
    { carrier := {g : G | ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
      one_mem' := by
        show ρ.quotient T hst 1 _ = _
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        have hb' : ρ.quotient T hst b (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := hb
        show ρ.quotient T hst (a * b) _ = _
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        show ρ.quotient T hst a⁻¹ _ = _
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine H.isOpen_of_mem_nhds (g := 1) ?_
  have h1 : {g : G | ρ g u = u} ∈ nhds (1 : G) :=
    (h u).mem_nhds (by
      show ρ 1 u = u
      rw [map_one]
      rfl)
  refine Filter.mem_of_superset h1 ?_
  intro g hg
  have hg' : ρ g u = u := hg
  show ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  have e : ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (ρ g u) := rfl
  rw [e, hg']

end UpperTheory.Reformulated.B.Gwb5
end

