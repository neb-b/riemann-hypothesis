module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0070
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem unit_of_res {R : Type} [CommRing R] [IsLocalRing R] {x : R} (h : IsUnit (residue R x)) :
    IsUnit x :=
  (residue_ne_zero_iff_isUnit x).1 h.ne_zero

theorem UpperTheory.V.UnitaryThreeInertia.exists_canon :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → (∀ a b, a ≠ b → X a b ∈ maximalIdeal R) → ∃ h, Canon X h :=
  _root_.UpperTheory.Reformulated.B.Qf19.exists_canon
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftAlongSurjectionGraded
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) :=
  _root_.UpperTheory.Reformulated.B.H71.map_tor f t

private theorem map_conjBy {A B D : Type} [CommRing A] [CommRing B] [Group D] (f : A →+* B) (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    (GG.map f).comp (conjBy h r) = conjBy (GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
    unfold GG.map
    rw [SemidirectProduct.map_inl]
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

private theorem conj_conj {A D : Type} [CommRing A] [Group D] (h h' : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem conj_one {A D : Type} [CommRing A] [Group D]
    (r : D →* GG (m := 3) (R := A)) : conjBy 1 r = r := by
  ext1 g
  simp [conjBy]

private theorem conj_mat {A D : Type} [CommRing A] [Group D] (h : GL (Fin 3) A)
    (r : D →* GG (m := 3) (R := A)) (g : D) :
    (conjBy h r g).mat = (h : Matrix _ _ A) * (r g).mat *
      ((sgnAct 3 A (r g).right h⁻¹ : GL (Fin 3) A) : Matrix _ _ A) := by
  have : (conjBy h r g).left = h * (r g).left * sgnAct 3 A (r g).right h⁻¹ := by
    simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [GG.mat, this, Units.val_mul]

private theorem setup {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ)
    (hg : F.Marked g₁) {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    (r : Γ →* GG (m := 3) (R := R))
    (hr : Red F.η F.Ψ r) :
    ∃ Ψ : Γ →* (ResidueField R)ˣ, IsUnit (2 : R) ∧ Marks F.η Ψ F.c g₁ ∧
      (GG.map (residue R)).comp r = r0 F.η Ψ := by
  refine ⟨(Units.map ((residue R).comp (algebraMap O R)).toMonoidHom).comp F.Ψ, ?_,
    ⟨hF.csq, hF.ηc, by simp [hF.Ψc], hg.1, ?_⟩, ?_⟩
  · simpa [map_ofNat] using hF.two.map (algebraMap O R)
  · simpa using hg.2.map ((residue R).comp (algebraMap O R))
  · refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.mult g)
    rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
    ext a b
    exact Ideal.Quotient.eq.2 (hr.red g a b)

theorem UpperTheory.lift_along_surjection_graded :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
      [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι),
      F.Ok → ∀ g₁, F.Marked g₁ → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
        [CommRing R'] [Algebra O R'] [IsCO O R'] (q : R →ₐ[O] R'), Function.Surjective q →
      ∀ (r : Γ →* GG (m := 3) (R := R)) (r' : Γ →* GG (m := 3) (R := R')),
        F.Cond r → IsLocallyConstant (mats r) → push q r = r' → F.CondN g₁ r' →
        ∃ r₂ : Γ →* GG (m := 3) (R := R), F.IsPt g₁ r₂ ∧ push q r₂ = r' := by
  intro O _ _ G Γ ι _ _ _ _ _ F hF g₁ hg R R' _ _ _ _ _ _ q hq r r' hr hlc hp hr'
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hm : ∀ x : R, q x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
  have hent : ∀ (h : GL (Fin 3) R), InHat (GeneralLinearGroup.map (q : R →+* R') h) ↔ InHat h := fun h => by
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← hm]
    refine iff_of_eq (congrArg (· ∈ maximalIdeal R') ?_)
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  obtain ⟨Ψ, h2, hM, hred⟩ := setup F hF g₁ hg r hr.toRed
  obtain ⟨Ψ', h2', hM', hred'⟩ := setup F hF g₁ hg r' hr'.toRed
  obtain ⟨h, hh, hN⟩ := exists_normalised F.η Ψ F.c g₁ r h2 hM hred
  have hpush : ∀ H : GL (Fin 3) R, push q (conjBy H r) =
      conjBy (GeneralLinearGroup.map (q : R →+* R') H) r' := fun H => by
    rw [← hp]; exact map_conjBy _ _ _
  have hN' : Normalised F.c g₁ (conjBy (GeneralLinearGroup.map (q : R →+* R') h) r') := by
    rw [← hpush]
    refine ⟨?_, ?_, ?_⟩
    · rw [MonoidHom.comp_apply, GG.map_mat, hN.atc, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := congrArg q hN.z12
      simpa [zmat] using this
    · have := congrArg q hN.z21
      simpa [zmat] using this
  obtain ⟨t', -, ht'⟩ := normalised_unique F.η Ψ' F.c g₁ r' _ h2' hM' hred' ((hent h).2 hh) hr'.norm hN'
  obtain ⟨t₀, ht₀⟩ := hq t'
  obtain ⟨t, rfl⟩ : IsUnit t₀ := by
    by_contra hn
    have := (hm t₀).2 hn
    rw [ht₀] at this
    exact this t'.isUnit
  have ht : Units.map (q : R →+* R').toMonoidHom t = t' := Units.ext ht₀
  have hH : GeneralLinearGroup.map (q : R →+* R') (tor R t⁻¹ * h) = 1 := by
    rw [map_mul, ht', map_tor, map_inv, ht, map_inv, inv_mul_cancel]
  have hHhat : InHat (tor R t⁻¹ * h) := by
    rw [← hent, hH]
    intro a b
    simp
  refine ⟨conjBy (tor R t⁻¹ * h) r, ⟨⟨(cond_conj F _ hHhat).2 r hr, ?_⟩, fun n => ?_⟩, ?_⟩
  · rw [conj_conj]
    exact (conjBy_tor _ _).2.2.1 _ _ hN
  · generalize tor R t⁻¹ * h = H
    have := (hlc.prodMk hF.η_cont).comp fun p : Matrix (Fin 3) (Fin 3) R × ℤˣ =>
      ((H : Matrix _ _ R) * p.1 * ((sgnAct 3 R p.2 H⁻¹ : GL (Fin 3) R) : Matrix _ _ R)).map
        (Ideal.Quotient.mk (maximalIdeal R ^ n))
    convert this using 1
    funext g
    rw [conj_mat, hr.mult g]
    rfl
  · rw [hpush, hH, conj_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtCorr
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I M : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := fun a b => by
  have h : EntIn I Xᵀ := fun a b => hX b a
  exact I.neg_mem (entIn_mul_right _ (entIn_mul_left _ h) a b)

private theorem entIn_ite (s : ℤˣ) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (if s = 1 then X else thetaLie X) := by
  split_ifs
  · exact hX
  · exact entIn_thetaLie hX

private theorem entIn_adFun (x : GG (m := m) (R := C)) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (x.adFun X) :=
  entIn_mul_right _ (entIn_mul_left _ (entIn_ite _ hX))

private theorem entIn_mul_zero (hI : M * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn M X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := Ideal.mul_mem_mul (hX a k) (hY k b)
  rwa [hI, Ideal.mem_bot] at this

private theorem adFun_congr (hI : M * I = ⊥) {x y : GG (m := m) (R := C)} (hr : x.right = y.right)
    (hm : EntIn M (x.mat - y.mat)) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    x.adFun X = y.adFun X := by
  unfold GG.adFun
  rw [hr]
  have hY := entIn_ite y.right hX
  generalize (if y.right = 1 then X else thetaLie X) = Y at hY ⊢
  have h1 : x.mat * Y = y.mat * Y := by
    rw [← sub_eq_zero, ← Matrix.sub_mul]
    exact entIn_mul_zero hI hm hY
  have h2 : ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) -
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (x.mat - y.mat) *
        ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp only [GG.mat, Matrix.mul_sub, Matrix.sub_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [h1, eq_comm, ← sub_eq_zero, ← Matrix.mul_sub, h2]
  exact entIn_mul_zero (by rwa [mul_comm]) (entIn_mul_left _ hY)
    (entIn_mul_right _ (entIn_mul_left _ hm))

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem sgnAct_one_add (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [hq]
  · have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hq, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, entIn_mul_zero hI hX hX]
      simp
    rw [sgnAct_neg_one, theta_val, hinv]
    simp only [h, if_false, thetaLie, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat]
    rw [sub_eq_add_neg]

private structure Near (I : Ideal C) (y : GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C) : Prop where
  right : y.right = 1
  mat : y.mat = 1 + X
  ent : EntIn I X

private theorem act_act (s : ℤˣ) (g : GL (Fin m) C) : sgnAct m C s (sgnAct m C s g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]

private theorem Near.mul_mat {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (h : Near I y X) (x : GG (m := m) (R := C)) :
    (y * x).mat = (1 + X) * x.mat := by
  rw [← h.mat]
  simp [GG.mat, h.right]

private theorem Near.mul (hI : I * I = ⊥) {y y' : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X') : Near I (y * y') (X + X') := by
  refine ⟨by simp [h.right, h'.right], ?_, fun a b => I.add_mem (h.ent a b) (h'.ent a b)⟩
  rw [h.mul_mat, h'.mat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, entIn_mul_zero hI h.ent h'.ent,
    Matrix.mul_one]
  abel

private theorem Near.conj (hI : I * I = ⊥) {y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (x : GG (m := m) (R := C)) : Near I (x * y * x⁻¹) (x.adFun X) := by
  refine ⟨by simp [h.right], ?_, entIn_adFun x h.ent⟩
  have e : (x * y * x⁻¹).left = x.left * sgnAct m C x.right y.left * x.left⁻¹ := by
    simp [h.right, act_act]
  rw [GG.mat, e, Units.val_mul, Units.val_mul, sgnAct_one_add hI _ _ h.ent h.mat, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Units.mul_inv]
  rfl

private theorem Near.uniq {y : GG (m := m) (R := C)} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y X') : X = X' :=
  add_left_cancel (h.mat.symm.trans h'.mat)

private theorem Near.eq {y y' : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X) : y = y' := by
  ext1
  · exact Units.ext (h.mat.trans h'.mat.symm)
  · rw [h.right, h'.right]

private theorem exists_near (hI : I * I = ⊥) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    ∃ y : GG (m := m) (R := C), Near I y X :=
  ⟨⟨onePlus X (entIn_mul_zero hI hX hX), 1⟩, rfl, rfl, hX⟩

private theorem near_of {x y : GG (m := m) (R := C)} {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (hr : x.right = y.right) (hm : x.mat = (1 + X) * y.mat) : Near I (x * y⁻¹) X := by
  refine ⟨by simp [hr], ?_, hX⟩
  have e : (x * y⁻¹).left = x.left * y.left⁻¹ := by simp [hr, act_act]
  rw [GG.mat, e, Units.val_mul]
  change x.mat * _ = _
  rw [hm, GG.mat, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.lt_corr :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → K ≤ maximalIdeal R → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ s : D → GG (m := 3) (R := R), IsLocallyConstant s → (∀ g, (s g).right = η g) →
      (∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R))) →
      (∀ g h, ∃ c ∈ gw R j, EntIn K c ∧ (s g * s h).mat = (1 + c) * (s (g * h)).mat) →
      ∃ r : D →* GG (m := 3) (R := R), IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧ ∃ b ∈ gw R j, EntIn K b ∧ (r g).mat = (1 + b) * (s g).mat := by
  intro O R D _ _ _ _ _ _ _ _ _ η Ψ K j hK hle hH s hs hη hred hc
  have hKK : K * K = ⊥ := le_bot_iff.1 (hK ▸ Ideal.mul_mono_left hle)
  choose c hcw hcK hcm using hc
  have hu : ∀ g h, Near K (s g * s h * (s (g * h))⁻¹) (c g h) := fun g h =>
    near_of (hcK g h) (by simp [hη]) (hcm g h)
  have had : ∀ g {X : Matrix (Fin 3) (Fin 3) R}, EntIn K X →
      (s g).adFun X = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g X := fun g X hX =>
    adFun_congr hK (y := GG.map (algebraMap O R) (r0 η Ψ g)) (hη g) (hred g) hX
  have hlc : IsLocallyConstant fun z : D × D => c z.1 z.2 := by
    have e : (fun z : D × D => c z.1 z.2) =
        (fun w : (GG (m := 3) (R := R) × GG (m := 3) (R := R)) × GG (m := 3) (R := R) => (w.1.1 * w.1.2 * w.2⁻¹).mat - 1) ∘
          fun z : D × D => ((s z.1, s z.2), s (z.1 * z.2)) := by
      funext z
      simp only [Function.comp_apply, (hu z.1 z.2).mat, add_sub_cancel_left]
    rw [e]
    exact (((hs.comp_continuous continuous_fst).prodMk (hs.comp_continuous continuous_snd)).prodMk
      (hs.comp_continuous continuous_mul)).comp _
  obtain ⟨b, hb, hbw, hbK, hbe⟩ := lifting_obstruction_second_cohomology η Ψ K j hK hH (fun z => c z.1 z.2) hlc (fun z => hcw _ _)
    (fun z => hcK _ _) (fun g h k => by
      have h1 := (hu g h).mul hKK (hu (g * h) k)
      have h2 := ((hu h k).conj hKK (s g)).mul hKK (hu g (h * k))
      have e : s g * s h * (s (g * h))⁻¹ * (s (g * h) * s k * (s (g * h * k))⁻¹) =
          s g * (s h * s k * (s (h * k))⁻¹) * (s g)⁻¹ * (s g * s (h * k) * (s (g * (h * k)))⁻¹) := by
        rw [mul_assoc g h k]; group
      rw [e] at h1
      have h3 := h1.uniq h2
      rw [had g (hcK h k)] at h3
      dsimp only
      rw [sub_add_eq_add_sub, ← h3]
      abel)
  have hnb : ∀ g, EntIn K (-b g) := fun g a a' => K.neg_mem (hbK g a a')
  choose e he using fun g => exists_near hKK (hnb g)
  have hmul : ∀ g h, e (g * h) * s (g * h) = e g * s g * (e h * s h) := fun g h => by
    have h1 := ((he g).mul hKK ((he h).conj hKK (s g))).mul hKK (hu g h)
    have h2 : -b g + (s g).adFun (-b h) + c g h = -b (g * h) := by
      have := hbe g h
      dsimp only at this
      rw [had g (hnb h), map_neg, this]
      abel
    rw [h2] at h1
    rw [← h1.eq (he (g * h))]
    group
  refine ⟨MonoidHom.mk' (fun g => e g * s g) hmul, ?_, fun g => ⟨?_, -b g, neg_mem (hbw g), hnb g,
    (he g).mul_mat _⟩⟩
  · have e' : mats (MonoidHom.mk' (fun g => e g * s g) hmul) =
        (fun w : Matrix (Fin 3) (Fin 3) R × GG (m := 3) (R := R) => (1 + -w.1) * w.2.mat) ∘ fun g => (b g, s g) := by
      funext g
      exact (he g).mul_mat _
    rw [e']
    exact (hb.prodMk hs).comp _
  · show (e g * s g).right = η g
    simp [(he g).right, hη]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Origin
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc {O A σ : Type} [CommRing O] [CommRing A] [Fintype σ]
    (φ : MvPowerSeries σ O →+* A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O)
    (hp : MvPowerSeries.constantCoeff p = 0) : φ p = 0 := by
  classical
  have hsupp : ∀ n : σ →₀ ℕ, n ≠ 0 → n.support.Nonempty :=
    fun n hn => Finsupp.support_nonempty_iff.mpr hn
  let sel : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : n ≠ 0, (hsupp n h).choose = i
  let q : σ → MvPowerSeries σ O := fun i m =>
    if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0
  have hX : ∀ (n : σ →₀ ℕ) (i : σ) (f : MvPowerSeries σ O),
      MvPowerSeries.coeff n (MvPowerSeries.X i * f)
        = if Finsupp.single i 1 ≤ n then MvPowerSeries.coeff (n - Finsupp.single i 1) f else 0 := by
    intro n i f
    rw [show (MvPowerSeries.X i : MvPowerSeries σ O) = MvPowerSeries.monomial (Finsupp.single i 1) 1
      from rfl, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hq : ∀ (i : σ) (m : σ →₀ ℕ), MvPowerSeries.coeff m (q i)
      = if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0 :=
    fun i m => rfl
  have hdec : p = ∑ i, MvPowerSeries.X i * q i := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hX, hq]
    by_cases hn : n = 0
    · subst hn
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hle
      have := hle i
      simp at this
    · set j := (hsupp n hn).choose with hj
      have hjmem : j ∈ n.support := (hsupp n hn).choose_spec
      have hjle : Finsupp.single j 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjmem)
      rw [Finset.sum_eq_single j]
      · rw [if_pos hjle, tsub_add_cancel_of_le hjle, if_pos ⟨hn, rfl⟩]
      · intro b _ hb
        by_cases hble : Finsupp.single b 1 ≤ n
        · rw [if_pos hble, tsub_add_cancel_of_le hble, if_neg]
          rintro ⟨_, hb'⟩
          exact hb hb'.symm
        · rw [if_neg hble]
      · intro h
        exact absurd (Finset.mem_univ j) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, hφ, zero_mul]

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_cc {O σ : Type} [CommRing O] [Fintype σ]
    (φ : MvPowerSeries σ O →ₐ[O] O) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O) :
    φ p = MvPowerSeries.constantCoeff p := by
  have h0 : MvPowerSeries.constantCoeff
      (p - algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr rfl
  have h := UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* O) (fun i => hφ i) _ h0
  rw [map_sub, sub_eq_zero] at h
  have h2 : φ (algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p))
      = MvPowerSeries.constantCoeff p := by
    rw [AlgHom.commutes]
    rfl
  exact h.trans h2

theorem UpperTheory.V.UnitaryThreeInertia.hasOrigin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∃ h : W.HasOrigin, push (W.origin h) u = r0 F.η F.Ψ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW
  obtain ⟨f, hf, -⟩ := hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)
  have hz : ∀ i, f (W.z i) = 0 := by
    intro i
    obtain ⟨g, a, b, -, -, hzi⟩ := hW.var i
    rw [hzi, map_sub]
    have h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b := by
      rw [← hf]
      rfl
    have h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b := by
      show f (algebraMap O R _) = _
      rw [AlgHom.commutes]
      rfl
    rw [h1, h2, sub_self]
  haveI := W.fin
  let ψ : MvPowerSeries W.σ O →ₐ[O] O := f.comp W.π
  have hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p :=
    UpperTheory.V.UnitaryThreeInertia.map_eq_cc ψ (fun i => hz i)
  have hO : W.HasOrigin := by
    intro p hp
    rw [← hψ]
    show f (W.π p) = 0
    rw [hp, map_zero]
  refine ⟨hO, ?_⟩
  have heq : W.origin hO = f := by
    ext x
    obtain ⟨p, rfl⟩ := W.surj x
    rw [UpperTheory.V.Alg.WPres.origin_π, ← hψ]
    rfl
  rw [heq, hf]
  exact MonoidHom.ext fun g => rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.SmoothPtWeightedGradedAlgebraBasePoint
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

theorem UpperTheory.smoothPt_weightedGradedAlgebra_basePoint :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ),
        SmoothPt (Fgr O wt) (x0 O wt) (fun j => Nat.card {i // wt i = j}) := by
  intro O _ _ σ hσ wt
  classical
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  let φ : FA O wt →ₐ[O] MvPowerSeries σ (FractionRing O) :=
    (MvPowerSeries.mapAlgHom (Algebra.ofId O (FractionRing O))).comp (WPres.free O wt).A.val
  have hφ : ∀ (f : FA O wt) (d : σ →₀ ℕ),
      coeff d (φ f) = algebraMap O (FractionRing O) (coeff d (ser f)) := fun f d => rfl
  refine ⟨σ, hσ, wt, φ, ⟨?_, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro j f hf d hd
    rw [hφ, mem_Fgr.1 hf d hd, map_zero]
  · intro f
    rw [weightedSeriesOrigin_apply]
    exact hφ f 0
  · intro i
    have hz : ser ((WPres.free O wt).zA i) = MvPowerSeries.X i := rfl
    refine ⟨(WPres.free O wt).zA i, ?_, fun i' hi => ?_⟩
    · rw [hφ, hz, coeff_index_single_self_X, map_one]
      exact one_ne_zero
    · rw [hφ, hz, coeff_index_single_X, if_neg hi, map_zero]
  · intro f h0 h1
    refine (UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero O σ wt f).2 ⟨by rw [← weightedSeriesOrigin_apply, h0], fun i => hinj ?_⟩
    rw [← hφ, h1, map_zero]
end

