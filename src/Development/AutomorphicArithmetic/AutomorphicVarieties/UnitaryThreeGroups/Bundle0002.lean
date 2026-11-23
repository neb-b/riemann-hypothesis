module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
section
open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ}

private theorem entIn_mul_left (I : Ideal C) (A X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (I : Ideal C) (A X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem mul_eq_zero_of_entIn (I : Ideal C) (hI : I * I = ⊥) (X Y : Matrix (Fin m) (Fin m) C)
    (hX : EntIn I X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  have h := Ideal.mul_mem_mul (hX a k) (hY k b)
  rw [hI, Ideal.mem_bot] at h
  exact h

private theorem entIn_thetaLie (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) :
    EntIn I (thetaLie X) := by
  intro a b
  simp only [thetaLie, Matrix.neg_apply]
  exact I.neg_mem (entIn_mul_right I _ _ (entIn_mul_left I _ _ (fun i j => hX j i)) a b)

private theorem sgnAct_one_add (I : Ideal C) (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have hXX : X * X = 0 := mul_eq_zero_of_entIn I hI X X hX hX
  by_cases hs : s = 1
  · subst hs
    rw [if_pos rfl, map_one, MulAut.one_apply, hq]
  · have hs' : s = -1 := by
      rcases Int.units_eq_one_or s with h | h
      · exact absurd h hs
      · exact h
    subst hs'
    rw [sgnAct_neg_one, theta_val, if_neg hs]
    have h1 : (q : Matrix (Fin m) (Fin m) C) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (1 - X) * (q : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [hq, sub_mul, one_mul, mul_add, mul_one, hXX, add_zero, add_sub_cancel_right]
    have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      calc ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C)
          = ((1 - X) * (q : Matrix (Fin m) (Fin m) C)) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
            rw [h2, one_mul]
        _ = (1 - X) * ((q : Matrix (Fin m) (Fin m) C) * ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C)) := mul_assoc _ _ _
        _ = 1 - X := by rw [h1, mul_one]
    rw [hinv, Matrix.transpose_sub, Matrix.transpose_one, mul_sub, sub_mul, mul_one, Jmat_mul_Jmat, thetaLie,
      sub_eq_add_neg]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_isCoc :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C) (r r' : G →* GG (m := m) (R := C)), I * I = ⊥ →
      (GG.map (Ideal.Quotient.mk I)).comp r' = (GG.map (Ideal.Quotient.mk I)).comp r →
      ∃ γ : G → Matrix (Fin m) (Fin m) C, (∀ g, EntIn I (γ g)) ∧ IsCoc r γ ∧ IsDeform r γ r' := by
  intro G C _ _ m I r r' hI hr
  have hR : ∀ g, (r' g).right = (r g).right := by
    intro g
    have h := congrArg SemidirectProduct.right (DFunLike.congr_fun hr g)
    simpa [GG.map] using h
  have hM : ∀ g, ((r' g).left : Matrix (Fin m) (Fin m) C).map (Ideal.Quotient.mk I)
      = ((r g).left : Matrix (Fin m) (Fin m) C).map (Ideal.Quotient.mk I) := by
    intro g
    have h := congrArg GG.mat (DFunLike.congr_fun hr g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, GG.map_mat, GG.map_mat] at h
    exact h
  obtain ⟨q, hqdef⟩ : ∃ q : G → GL (Fin m) C, ∀ g, q g = (r' g).left * ((r g).left)⁻¹ := ⟨_, fun _ => rfl⟩
  have hE : ∀ g, EntIn I ((q g : Matrix (Fin m) (Fin m) C) - 1) := by
    intro g a b
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : (Ideal.Quotient.mk I).mapMatrix ((q g : Matrix (Fin m) (Fin m) C) - 1) = 0 := by
      rw [map_sub, map_one, hqdef, Units.val_mul, map_mul, RingHom.mapMatrix_apply, hM g,
        ← RingHom.mapMatrix_apply, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, sub_self]
    have h2 := congrFun (congrFun h1 a) b
    simpa using h2
  refine ⟨fun g => (q g : Matrix (Fin m) (Fin m) C) - 1, hE, ?_, ?_⟩
  · intro g h
    have hq : q (g * h) = q g * ((r g).left * sgnAct m C (r g).right (q h) * ((r g).left)⁻¹) := by
      simp only [hqdef, map_mul, SemidirectProduct.mul_left, hR g, map_inv]
      group
    have had : ∀ Y, adRep r g Y = (((r g).left : Matrix (Fin m) (Fin m) C) * (if (r g).right = 1 then Y else thetaLie Y))
        * ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := fun Y => rfl
    have hφ := sgnAct_one_add I hI (q h) _ (hE h) (by abel) (r g).right
    have hAA : ((r g).left : Matrix (Fin m) (Fin m) C) * ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hYE : EntIn I (if (r g).right = 1 then (q h : Matrix (Fin m) (Fin m) C) - 1 else thetaLie ((q h : Matrix (Fin m) (Fin m) C) - 1)) := by
      split_ifs
      · exact hE h
      · exact entIn_thetaLie I _ (hE h)
    show (q (g * h) : Matrix (Fin m) (Fin m) C) - 1 = ((q g : Matrix (Fin m) (Fin m) C) - 1) + adRep r g ((q h : Matrix (Fin m) (Fin m) C) - 1)
    rw [had, hq]
    simp only [Units.val_mul]
    rw [hφ]
    generalize (if (r g).right = 1 then (q h : Matrix (Fin m) (Fin m) C) - 1 else thetaLie ((q h : Matrix (Fin m) (Fin m) C) - 1)) = Y at hYE ⊢
    generalize ((r g).left : Matrix (Fin m) (Fin m) C) = A at hAA ⊢
    generalize ((((r g).left)⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = B at hAA ⊢
    have e1 : A * (1 + Y) * B = 1 + A * Y * B := by
      rw [mul_add, mul_one, add_mul, hAA]
    rw [e1]
    have hAY : EntIn I (A * Y * B) := entIn_mul_right I B (A * Y) (entIn_mul_left I A Y hYE)
    have hN := mul_eq_zero_of_entIn I hI ((q g : Matrix (Fin m) (Fin m) C) - 1) (A * Y * B) (hE g) hAY
    generalize A * Y * B = M at hN ⊢
    generalize (q g : Matrix (Fin m) (Fin m) C) = Q at hN ⊢
    have e2 : Q * (1 + M) = Q + M + (Q - 1) * M := by noncomm_ring
    rw [e2, hN]
    abel
  · intro g
    refine ⟨hR g, ?_⟩
    simp only [GG.mat]
    rw [add_sub_cancel, hqdef, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsLieElementMiddleBlockPart
section
open Matrix UpperTheory.V.U3

private theorem corner_eq' {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    corner X = !![X 0 0, X 0 2; X 2 0, X 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem corner_mul' {R : Type} [CommRing R] (X Y : Matrix (Fin 3) (Fin 3) R)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) : corner (X * Y) = corner X * corner Y := by
  simp only [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h2]

private theorem corner_one' {R : Type} [CommRing R] : corner (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  rw [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem corner_theta' {R : Type} [CommRing R] (a : GL (Fin 3) R)
    (h0 : (a : Matrix (Fin 3) (Fin 3) R) 0 1 = 0) (h2 : (a : Matrix (Fin 3) (Fin 3) R) 2 1 = 0)
    (hd : (corner (a : Matrix (Fin 3) (Fin 3) R)).det = 1) :
    corner (theta a : Matrix (Fin 3) (Fin 3) R) =
      Matrix.diagonal ![-1, 1] * corner (a : Matrix (Fin 3) (Fin 3) R) * Matrix.diagonal ![-1, 1] := by
  have h1 : corner (a : Matrix (Fin 3) (Fin 3) R) *
      corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := by
    rw [← corner_mul' _ _ h0 h2, Units.mul_inv, corner_one']
  have h3 : corner ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate := by
    have := congrArg (fun Z => (corner (a : Matrix (Fin 3) (Fin 3) R)).adjugate * Z) h1
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul,
      Matrix.mul_one] using this
  rw [theta_val]
  generalize ((a⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = Y at h3
  generalize (a : Matrix (Fin 3) (Fin 3) R) = X at h3
  rw [Matrix.adjugate_fin_two] at h3
  have e00 : Y 0 0 = X 2 2 := by simpa [corner] using congrFun (congrFun h3 0) 0
  have e01 : Y 0 2 = - X 0 2 := by simpa [corner] using congrFun (congrFun h3 0) 1
  have e10 : Y 2 0 = - X 2 0 := by simpa [corner] using congrFun (congrFun h3 1) 0
  have e11 : Y 2 2 = X 0 0 := by simpa [corner] using congrFun (congrFun h3 1) 1
  simp only [corner_eq']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev,
      Matrix.diagonal, e00, e01, e10, e11]

theorem UpperTheory.V.U3.exists_lieElement_middleBlockPart :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := R)) (c : G), HasMult η r → η c = -1 → (r c).mat = 1 → Block η r →
      (∀ g ∈ η.ker, (corner (r g).mat).det = 1) →
      ∃ W : G →* GL (Fin 2) R, (∀ g, (W g : Matrix (Fin 2) (Fin 2) R) = Wfun r g) ∧ ∀ g, (W g : Matrix (Fin 2) (Fin 2) R).det = ((η g : ℤˣ) : ℤ) := by
  intro G R _ _ η r c hm hc hrc hB hd
  have hne : ((-1 : ℤˣ) = 1) = False := by decide
  have key : ∀ g, ∃ k ∈ η.ker, (r g).mat = (r k).mat := by
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact ⟨g, hg, rfl⟩
    · have hk : η (g * c⁻¹) = 1 := by rw [map_mul, map_inv, hg, hc, mul_inv_cancel]
      refine ⟨g * c⁻¹, hk, ?_⟩
      have e : r g = r (g * c⁻¹) * r c := by rw [← map_mul, inv_mul_cancel_right]
      have hr : (r (g * c⁻¹)).right = 1 := (hm _).trans hk
      rw [e]
      simp only [GG.mat] at hrc ⊢
      rw [SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]
  have h0 : ∀ g, (r g).mat 0 1 = 0 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hB k hk 0 1 (by decide)
  have h2 : ∀ g, (r g).mat 2 1 = 0 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hB k hk 2 1 (by decide)
  have hdet : ∀ g, (corner (r g).mat).det = 1 := fun g => by
    obtain ⟨k, hk, e⟩ := key g
    rw [e]; exact hd k hk
  have hD : (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) R) * Matrix.diagonal ![-1, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hp : ∀ g h, (r g).right = 1 →
      corner (r (g * h)).mat = corner (r g).mat * corner (r h).mat := by
    intro g h hg
    rw [← corner_mul' _ _ (h0 g) (h2 g), map_mul]
    simp only [GG.mat]
    rw [SemidirectProduct.mul_left, hg, sgnAct_one, Units.val_mul]
  have hn : ∀ g h, (r g).right = -1 →
      corner (r (g * h)).mat = corner (r g).mat *
        (Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1]) := by
    intro g h hg
    have : corner (theta (r h).left : Matrix (Fin 3) (Fin 3) R) =
        Matrix.diagonal ![-1, 1] * corner (r h).mat * Matrix.diagonal ![-1, 1] :=
      corner_theta' (r h).left (h0 h) (h2 h) (hdet h)
    rw [← this, ← corner_mul' _ _ (h0 g) (h2 g), map_mul]
    simp only [GG.mat]
    rw [SemidirectProduct.mul_left, hg, sgnAct_neg_one, Units.val_mul]
  let W0 : G →* Matrix (Fin 2) (Fin 2) R :=
    { toFun := Wfun r
      map_one' := by simp [Wfun, GG.mat, corner_one']
      map_mul' := fun g h => by
        have hgh : (r (g * h)).right = (r g).right * (r h).right := by
          rw [map_mul, SemidirectProduct.mul_right]
        rcases Int.units_eq_one_or (r g).right with hg | hg <;>
          rcases Int.units_eq_one_or (r h).right with hh | hh
        · simp only [Wfun, hgh, hg, hh, mul_one, if_true, hp g h hg]
        · simp only [Wfun, hgh, hg, hh, one_mul, if_true, hne, if_false, hp g h hg,
            Matrix.mul_assoc]
        · simp only [Wfun, hgh, hg, hh, mul_one, if_true, hne, if_false, hn g h hg,
            Matrix.mul_assoc, hD]
        · simp only [Wfun, hgh, hg, hh, neg_mul_neg, mul_one, if_true, hne, if_false, hn g h hg,
            Matrix.mul_assoc] }
  refine ⟨W0.toHomUnits, fun g => rfl, fun g => ?_⟩
  change (Wfun r g).det = _
  rw [← hm g]
  rcases Int.units_eq_one_or (r g).right with hg | hg
  · simp [Wfun, hg, hdet]
  · simp [Wfun, hg, hne, hdet, Fin.prod_univ_two]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar
section
open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.mat_gstar :
    ∀ {G R : Type} [Group G] [CommRing R] {m : ℕ} (r : G →* GG (m := m) (R := R)) (c g : G),
      (r c).mat = 1 → (r c).right = -1 → (r g).right = 1 →
      (r (gstar c g)).mat = Jmat (R := R) m * (r g).matᵀ * Jmat (R := R) m ∧
        (r (gstar c g)).right = 1 := by
  intro G R _ _ m r c g h1 h2 h3
  have hc : r c = SemidirectProduct.mk 1 (-1) := by
    apply SemidirectProduct.ext
    · exact Units.ext (by simpa [GG.mat] using h1)
    · exact h2
  have hg : r g = SemidirectProduct.mk (r g).left 1 := SemidirectProduct.ext rfl h3
  have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by
    simp only [gstar, map_mul, map_inv]
  rw [hs, hc, hg]
  simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, inv_one, map_one, mul_one, one_mul, MulAut.one_apply, map_inv,
    sgnAct_neg_one, theta_inv_val]
  refine ⟨?_, ?_⟩
  · simp
  · norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormCob
section
open Matrix UpperTheory.V.U3

private theorem gstar_right_and_mat_of_right_neg_one_mat_one {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c g₁ : G)
    (hc : (r c).right = -1) (h1 : (r g₁).right = 1) (hN : (r c).mat = 1) :
    (r (gstar c g₁)).right = 1 ∧ (r (gstar c g₁)).mat = Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3 := by
  have hcl : (r c).left = 1 := Units.ext hN
  refine ⟨by simp [gstar, hc, h1], ?_⟩
  have hL : (r (gstar c g₁)).left = theta ((r g₁).left⁻¹) := by
    simp only [gstar, map_mul, map_inv, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_right, hcl, hc, h1]
    simp [sgnAct, thetaAut]
    have e1 : theta (1 : GL (Fin 3) R) = 1 := map_one (thetaAut 3 R)
    have e2 : theta ((r g₁).left⁻¹) = (theta (r g₁).left)⁻¹ := map_inv (thetaAut 3 R) _
    rw [e1, mul_one, e2]
  show ((r (gstar c g₁)).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [hL, theta_val, inv_inv]
  rfl

private theorem cob_mul_mat_eq_commutator_of_right_eq_one {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R))
    (X : Matrix (Fin 3) (Fin 3) R) (g : G) (hg : (r g).right = 1) :
    cob r X g * (r g).mat = X * (r g).mat - (r g).mat * X := by
  show (X - (r g).adFun X) * (r g).mat = _
  simp only [GG.adFun, hg, ite_true]
  show (X - (r g).mat * X * ((r g).left⁻¹ : GL (Fin 3) R)) * ((r g).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [sub_mul, mul_assoc, Units.inv_mul, mul_one]
  rfl

theorem UpperTheory.V.U3.normCoc_cob_iff :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c g₁ : G) (X : Matrix (Fin 3) (Fin 3) R), IsUnit (2 : R) → (r c).right = -1 → (r g₁).right = 1 →
      Normalised c g₁ r → IsUnit (zeta c g₁ r) → (NormCoc c g₁ r (cob r X) ↔ X ∈ unitaryThreeTorusLieAlgebra R) := by
  intro G R _ _ r c g₁ X h2 hc h1 hn hz
  obtain ⟨hsr, hsm⟩ := gstar_right_and_mat_of_right_neg_one_mat_one r c g₁ hc h1 hn.atc
  have hcl : (r c).left = 1 := Units.ext hn.atc
  have hA : cob r X c = X - thetaLie X := by
    show X - (r c).adFun X = _
    have hne : (r c).right ≠ 1 := by rw [hc]; decide
    simp only [GG.adFun, ite_eq_right hne, hn.atc, one_mul]
    rw [hcl, inv_one, Units.val_one, mul_one]
  have hW : zvar c g₁ r (cob r X) = X * ((r g₁).mat - Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3)
      - ((r g₁).mat - Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3) * X := by
    show cob r X g₁ * (r g₁).mat - cob r X (gstar c g₁) * (r (gstar c g₁)).mat = _
    rw [cob_mul_mat_eq_commutator_of_right_eq_one r X g₁ h1, cob_mul_mat_eq_commutator_of_right_eq_one r X _ hsr, hsm]
    noncomm_ring
  set M := (r g₁).mat with hM
  have z12 : M 0 1 - M 1 2 = 0 := by
    have h := hn.z12
    simp only [zmat, hsm] at h
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h
    linear_combination h
  have z21 : M 1 0 - M 2 1 = 0 := by
    have h := hn.z21
    simp only [zmat, hsm] at h
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h
    linear_combination h
  have hu : IsUnit (M 0 0 - M 2 2) := by
    have e : zeta c g₁ r = M 0 0 - M 2 2 := by
      simp only [zeta, zmat, hsm]
      simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]
      rfl
    rw [← e]; exact hz
  constructor
  · rintro ⟨ha, h12, h21⟩
    rw [hA] at ha
    rw [hW] at h12 h21
    have a00 := congrFun (congrFun ha 0) 0
    have a11 := congrFun (congrFun ha 1) 1
    have a02 := congrFun (congrFun ha 0) 2
    have a20 := congrFun (congrFun ha 2) 0
    have a01 := congrFun (congrFun ha 0) 1
    have a10 := congrFun (congrFun ha 1) 0
    simp [thetaLie, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at a00 a11 a02 a20 a01 a10
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h12 h21
    have x11 : X 1 1 = 0 := h2.mul_left_cancel (by linear_combination a11)
    have x02 : X 0 2 = 0 := h2.mul_left_cancel (by linear_combination a02)
    have x20 : X 2 0 = 0 := h2.mul_left_cancel (by linear_combination a20)
    have x01 : X 0 1 = 0 := hu.mul_left_cancel
      (by linear_combination -h12 + X 0 0 * z12 - X 0 2 * z21 - X 1 1 * z12)
    have x10 : X 1 0 = 0 := hu.mul_left_cancel
      (by linear_combination h21 - X 1 1 * z21 + X 0 0 * z21 - X 2 0 * z12)
    have x12 : X 1 2 = 0 := by linear_combination a01 - x01
    have x21 : X 2 1 = 0 := by linear_combination a10 - x10
    have x22 : X 2 2 = -X 0 0 := by linear_combination a00
    rw [unitaryThreeTorusLieAlgebra, Submodule.mem_span_singleton]
    refine ⟨X 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wt1, Matrix.diagonal, x01, x10, x02, x20, x11, x12, x21, x22] <;> ring
  · intro hX
    rw [unitaryThreeTorusLieAlgebra, Submodule.mem_span_singleton] at hX
    obtain ⟨a, rfl⟩ := hX
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev,
          Matrix.smul_apply, Matrix.diagonal_apply] <;> ring
    · rw [hW]
      simp [Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.diagonal]
      linear_combination a * z12
    · rw [hW]
      simp [Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.diagonal]
      linear_combination a * z21
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit
section
open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.zeta_reducible_rep_eq_sub_inv_and_isUnit :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (c g₁ : G), Marks η Ψ c g₁ →
    zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) ∧ IsUnit (zeta c g₁ (r0 η Ψ)) := by
  intro G R _ _ η Ψ c g₁ hm
  have hz : zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) := by
    have hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by
      simp [gstar, map_mul, map_inv, hm.Ψc]
    simp only [zeta, zmat, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.sub_apply, Matrix.diagonal_apply_eq, hs]
    simp [wt1]
  refine ⟨hz, ?_⟩
  rw [hz]
  have key : ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R)
      = (((Ψ g₁)⁻¹ : Rˣ) : R) * (((Ψ g₁ : Rˣ) : R) ^ 2 - 1) := by
    rw [mul_sub, mul_one, pow_two, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact (Units.isUnit _).mul hm.Ψg
end

