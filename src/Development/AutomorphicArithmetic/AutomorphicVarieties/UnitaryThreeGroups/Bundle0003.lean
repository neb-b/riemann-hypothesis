module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0055
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
section
open Matrix UpperTheory.V.U3

private theorem single_mem_of_diag {κ : Type} [Field κ] {m : ℕ} (d : Fin m → κ)
    (hd : Function.Injective d) (W : Submodule κ (Fin m → κ))
    (hW : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W) (v : Fin m → κ) (hv : v ∈ W) (i : Fin m)
    (hi : v i ≠ 0) : (Pi.single i 1 : Fin m → κ) ∈ W :=
  _root_.UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag d hd W hW v hv i hi

private theorem exists_coord_of_not_matIrr {G κ : Type} [Group G] [Field κ] {m : ℕ}
    (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) κ) (d : Fin m → κ)
    (hd : Function.Injective d) (g₁ g₂ : G) (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H)
    (hD : a g₁ - a g₂ = Matrix.diagonal d) (h : ¬ MatIrr H a) :
    ∃ S : Fin m → Prop, (∃ j, S j) ∧ (∃ i, ¬ S i) ∧
      ∀ i j, S j → ¬ S i → ∀ g ∈ H, a g i j = 0 := by
  classical
  unfold MatIrr at h
  push Not at h
  obtain ⟨W, hW, hb, ht⟩ := h
  have hWd : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W := fun v hv => by
    rw [← hD, Matrix.sub_mulVec]
    exact W.sub_mem (hW _ h₁ _ hv) (hW _ h₂ _ hv)
  have hs := single_mem_of_diag d hd W hWd
  refine ⟨fun j => (Pi.single j 1 : Fin m → κ) ∈ W, ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, hs v hv j hj⟩
  · by_contra hc
    push Not at hc
    apply ht
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ' v]
    exact W.sum_mem fun i _ => W.smul_mem _ (hc i)
  · intro i j hj hi g hg
    by_contra hc
    apply hi
    refine hs _ (hW g hg _ hj) i ?_
    simpa using hc

theorem UpperTheory.V.U3.shape_cases :
    ∀ {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := κ)) (c g₁ : G),
      (2 : κ) ≠ 0 → HasMult η r → η c = -1 → η g₁ = 1 →
      Normalised c g₁ r → zeta c g₁ r ≠ 0 → TypeI η r ∨ Upper η r ∨ Lower η r ∨ TypeII η r := by
  intro G κ _ _ η r c g₁ h2 hm hc hg hn hz
  have hc' : (r c).right = -1 := (hm c).trans hc
  have hstar (g : G) (hg : g ∈ η.ker) :
      (r (gstar c g)).mat = Jmat κ 3 * (r g).matᵀ * Jmat κ 3 ∧ (r (gstar c g)).right = 1 := by
    have hc₀ : r c = SemidirectProduct.mk 1 (-1) :=
      SemidirectProduct.ext (Units.ext (by simpa [GG.mat] using hn.atc)) hc'
    have hg₀ : r g = SemidirectProduct.mk (r g).left 1 :=
      SemidirectProduct.ext rfl ((hm g).trans hg)
    have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by simp [gstar]
    rw [hs, hc₀, hg₀]
    simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right, inv_one, map_one, mul_one,
      one_mul, MulAut.one_apply, map_inv, sgnAct_neg_one, theta_inv_val]
    exact ⟨by simp, by norm_num⟩
  have hst : ∀ g ∈ η.ker, gstar c g ∈ η.ker := fun g hg =>
    (hm _).symm.trans (hstar g hg).2
  have hJ (M : Matrix (Fin 3) (Fin 3) κ) (i j : Fin 3) :
      (Jmat (R := κ) 3 * Mᵀ * Jmat (R := κ) 3) i j = M j.rev i.rev := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  set ζ := zeta c g₁ r with hζ
  have hD : zmat c g₁ r = Matrix.diagonal ![ζ, 0, -ζ] := by
    have hZ (i j : Fin 3) : zmat c g₁ r i j = (r g₁).mat i j - (r g₁).mat j.rev i.rev := by
      simp only [zmat, Matrix.sub_apply, (hstar g₁ hg).1, hJ]
    have e0 : (0 : Fin 3).rev = 2 := rfl
    have e1 : (1 : Fin 3).rev = 1 := rfl
    have e2 : (2 : Fin 3).rev = 0 := rfl
    have h01 := hn.z12
    have h10 := hn.z21
    rw [hZ, e0, e1] at h01 h10
    ext i j
    rw [hZ]
    simp only [hζ, zeta, hZ 0 0, e0]
    fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, Matrix.diagonal] <;>
      first | linear_combination h01 | linear_combination -h01 |
        linear_combination h10 | linear_combination -h10
  have hne : ζ ≠ -ζ := fun h => hz (by
    have : (2 : κ) * ζ = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2)
  let Z : Fin 3 → Fin 3 → Prop := fun i j => ∀ g ∈ η.ker, (r g).mat i j = 0
  have hsym : ∀ i j : Fin 3, Z i j → Z j.rev i.rev := by
    intro i j h g hg
    have h1 := h _ (hst g hg)
    rwa [(hstar g hg).1, hJ] at h1
  have s10 : Z 1 0 → Z 2 1 := hsym 1 0
  have s21 : Z 2 1 → Z 1 0 := hsym 2 1
  have s01 : Z 0 1 → Z 1 2 := hsym 0 1
  have s12 : Z 1 2 → Z 0 1 := hsym 1 2
  have hU : Z 1 0 → Z 2 0 → Upper η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s10 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hL : Z 0 1 → Z 0 2 → Lower η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s01 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hB : Z 0 1 → Z 1 0 → Upper η r ∨ Lower η r ∨ TypeII η r := by
    intro h1 h2
    by_cases hI : MatIrr η.ker fun g => corner (r g).mat
    · refine Or.inr (Or.inr ⟨?_, hI⟩)
      intro g hg a b hab
      have := h1 g hg
      have := h2 g hg
      have := s01 h1 g hg
      have := s10 h2 g hg
      fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
    · have hinj : Function.Injective ![ζ, -ζ] := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all
      obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker _ ![ζ, -ζ] hinj g₁
        (gstar c g₁) hg (hst g₁ hg) (by
          ext i j
          have := congrFun (congrFun hD (![0, 2] i)) (![0, 2] j)
          refine Eq.trans this ?_
          fin_cases i <;> fin_cases j <;> simp) hI
      have h3 := hS i j hj hi
      fin_cases i <;> fin_cases j
      · exact absurd hj hi
      · exact Or.inr (Or.inl (hL h1 h3))
      · exact Or.inl (hU h2 h3)
      · exact absurd hj hi
  by_cases hI : TypeI η r
  · exact Or.inl hI
  right
  have hinj : Function.Injective ![ζ, 0, -ζ] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker (mats r) _ hinj g₁
    (gstar c g₁) hg (hst g₁ hg) hD hI
  have hS' : ∀ i j, S j → ¬ S i → Z i j := hS
  by_cases a0 : S 0 <;> by_cases a1 : S 1 <;> by_cases a2 : S 2
  · fin_cases i <;> contradiction
  · exact Or.inl (hU (s21 (hS' _ _ a1 a2)) (hS' _ _ a0 a2))
  · exact hB (s12 (hS' _ _ a2 a1)) (hS' _ _ a0 a1)
  · exact Or.inl (hU (hS' _ _ a0 a1) (hS' _ _ a0 a2))
  · exact Or.inr (Or.inl (hL (hS' _ _ a1 a0) (hS' _ _ a2 a0)))
  · exact hB (hS' _ _ a1 a0) (s21 (hS' _ _ a1 a2))
  · exact Or.inr (Or.inl (hL (s12 (hS' _ _ a2 a1)) (hS' _ _ a2 a0)))
  · fin_cases j <;> contradiction
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FreeEtaleSheafZmodExistsHomSendingGenerator
section
open Matrix UpperTheory.V.U3

private theorem offdiag_zero {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ) (z z' : κ)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hne : z' ≠ -z)
    (h : M * Matrix.diagonal ![z, 0, -z] = Matrix.diagonal ![z', 0, -z'] * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at e
  by_contra hM
  have e' := mul_right_cancel₀ hM e
  have hne' : z ≠ -z' := fun h => hne (by rw [h, neg_neg])
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {κ ι : Type} [Field κ] [IsAlgClosed κ] (m : Fin 3 → κ) (hm : ∀ i, m i ≠ 0)
    (a a' : ι → Matrix (Fin 3) (Fin 3) κ)
    (h1 : ∀ g i j, m i * a g i j = a' g i j * m j)
    (h2 : ∀ g i j, m j.rev * a g i j = a' g i j * m i.rev) :
    ∃ t : κˣ, ∀ g i j, a' g i j = ((t ^ wt i j : κˣ) : κ) * a g i j := by
  have h0 := hm 0
  have h1' := hm 1
  have h2' := hm 2
  have ha : ∀ g i j, a' g i j = m i / m j * a g i j := by
    intro g i j
    have := hm j
    field_simp
    linear_combination -h1 g i j
  by_cases hd : m 0 * m 2 = m 1 * m 1
  · refine ⟨Units.mk0 (m 0 / m 1) (div_ne_zero h0 h1'), fun g i j => ?_⟩
    rw [ha]
    congr 1
    have e2 : m 2 = m 1 * m 1 / m 0 := by field_simp; linear_combination hd
    fin_cases i <;> fin_cases j <;> simp [wt, wt1, e2, zpow_ofNat, h0, h1'] <;> field_simp
  · obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (m 0 / m 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact div_ne_zero h0 h2' (by simpa using hs)
    have hz : ∀ g i j, (m i * m i.rev - m j * m j.rev) * a g i j = 0 := by
      intro g i j
      linear_combination m i.rev * h1 g i j - m j * h2 g i j
    have hd1 : m 0 * m 2 - m 1 * m 1 ≠ 0 := sub_ne_zero.2 hd
    have hd2 : m 2 * m 0 - m 1 * m 1 ≠ 0 := by rwa [mul_comm (m 2)]
    have hd3 : m 1 * m 1 - m 0 * m 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
    have hd4 : m 1 * m 1 - m 2 * m 0 ≠ 0 := by rwa [mul_comm (m 2)]
    refine ⟨Units.mk0 s hs0, fun g i j => ?_⟩
    have z01 : a g 0 1 = 0 := (mul_eq_zero.1 (hz g 0 1)).resolve_left hd1
    have z21 : a g 2 1 = 0 := (mul_eq_zero.1 (hz g 2 1)).resolve_left hd2
    have z10 : a g 1 0 = 0 := (mul_eq_zero.1 (hz g 1 0)).resolve_left hd3
    have z12 : a g 1 2 = 0 := (mul_eq_zero.1 (hz g 1 2)).resolve_left hd4
    have e0 : m 0 = s * s * m 2 := by rw [← hs]; field_simp
    rw [ha]
    fin_cases i <;> fin_cases j <;>
      simp [wt, wt1, z01, z21, z10, z12, e0, zpow_ofNat, h1', h2', hs0] <;> left <;> field_simp

theorem UpperTheory.V.U3.conjBy_tor_of_iso :
    ∀ {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (η : G →* ℤˣ) (r r' : G →* GG (m := 3) (R := κ)) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → HasMult η r' →
      η c = -1 → η g₁ = 1 → Normalised c g₁ r → Normalised c g₁ r' → zeta c g₁ r ≠ 0 → zeta c g₁ r' ≠ 0 → zeta c g₁ r' ≠ -zeta c g₁ r →
      (TypeI η r ∨ TypeII η r) → MatIso η.ker (mats r) (mats r') → ∃ t : κˣ, r' = conjBy (tor κ t) r := by
  intro G κ _ _ _ η r r' c g₁ h2 hr hr' hc hg hN hN' hz hz' hne _ hiso
  obtain ⟨M, hM⟩ := hiso
  have hstar : ∀ g, η g = 1 → η (gstar c g) = 1 := by
    intro g h
    simp [gstar, hc, h]
  have hZ : (M : Matrix (Fin 3) (Fin 3) κ) * zmat c g₁ r = zmat c g₁ r' * M := by
    have e1 := hM g₁ hg
    have e2 := hM (gstar c g₁) (hstar g₁ hg)
    unfold mats at e1 e2
    rw [zmat, zmat, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [zmat_diag r c g₁ h2.isUnit ((hr c).trans hc) ((hr g₁).trans hg) hN,
    zmat_diag r' c g₁ h2.isUnit ((hr' c).trans hc) ((hr' g₁).trans hg) hN'] at hZ
  have hoff := offdiag_zero _ _ _ hz hz' hne hZ
  have hdiag : (M : Matrix (Fin 3) (Fin 3) κ) = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hm : ∀ i, (M : Matrix (Fin 3) (Fin 3) κ) i i ≠ 0 := by
    have hdet : (M : Matrix (Fin 3) (Fin 3) κ).det ≠ 0 := M.det_ne_zero
    rw [hdiag, Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  have h1 : ∀ g, η g = 1 → ∀ i j, M i i * (r g).mat i j = (r' g).mat i j * M j j := by
    intro g h i j
    have e := hM g h
    rw [hdiag] at e
    have e' := congrFun (congrFun e i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at e'
  have hJ : ∀ (X : Matrix (Fin 3) (Fin 3) κ) (i j : Fin 3),
      (Jmat (R := κ) 3 * Xᵀ * Jmat (R := κ) 3) j.rev i.rev = X i j := by
    intro X i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have h2' : ∀ g, η g = 1 → ∀ i j : Fin 3,
      M j.rev j.rev * (r g).mat i j = (r' g).mat i j * M i.rev i.rev := by
    intro g h i j
    have e := h1 _ (hstar g h) j.rev i.rev
    rwa [(mat_gstar r c g hN.atc ((hr c).trans hc) ((hr g).trans h)).1,
      (mat_gstar r' c g hN'.atc ((hr' c).trans hc) ((hr' g).trans h)).1, hJ, hJ] at e
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (ι := η.ker) (fun i => M i i) hm (fun g => (r g).mat)
    (fun g => (r' g).mat) (fun g => h1 g g.2) (fun g => h2' g g.2)
  have htor_val (u : κˣ) : (tor κ u : Matrix (Fin 3) (Fin 3) κ) =
      Matrix.diagonal (fun i => ((u ^ wt1 i : κˣ) : κ)) := rfl
  have htheta : theta (tor κ t) = tor κ t := by
    apply Units.ext
    rw [theta_val, ← map_inv, htor_val, htor_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, wt1, Matrix.diagonal, Fin.rev]
  have hact (s : ℤˣ) : sgnAct (m := 3) (R := κ) s (tor κ t) = tor κ t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp [htheta]
  have hleft (g : G) : (conjBy (tor κ t) r g).left = tor κ t * (r g).left * tor κ t⁻¹ := by
    simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hact, map_inv]
  have hright (g : G) : (conjBy (tor κ t) r g).right = (r g).right := by
    simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  have hmat (g : G) (i j : Fin 3) :
      (conjBy (tor κ t) r g).mat i j = ((t ^ wt i j : κˣ) : κ) * (r g).mat i j := by
    show (((conjBy (tor κ t) r g).left : GL (Fin 3) κ) : Matrix (Fin 3) (Fin 3) κ) i j = _
    rw [hleft, Units.val_mul, Units.val_mul, htor_val, htor_val, mul_diagonal, diagonal_mul]
    have hweight : ((t ^ wt1 i : κˣ) : κ) * ((t⁻¹ ^ wt1 j : κˣ) : κ) = ((t ^ wt i j : κˣ) : κ) := by
      rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
    rw [← hweight, GG.mat]
    ring
  refine ⟨t, ?_⟩
  have hker : ∀ g, η g = 1 → r' g = conjBy (tor κ t) r g := by
    intro g h
    refine SemidirectProduct.ext (Units.ext ?_) (by rw [hright, hr g, hr' g])
    ext i j
    exact (ht ⟨g, h⟩ i j).trans (hmat g i j).symm
  have hconj_c : (conjBy (tor κ t) r c).mat = 1 := by
    ext i j
    rw [hmat, hN.atc]
    by_cases hij : i = j
    · subst j
      simp [wt]
    · simp [Matrix.one_apply_ne hij]
  have hcc : r' c = conjBy (tor κ t) r c :=
    SemidirectProduct.ext (Units.ext (hN'.atc.trans hconj_c.symm))
      (by rw [hright, hr c, hr' c])
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (η g) with h | h
  · exact hker g h
  · have e : g = g * c⁻¹ * c := by simp
    rw [e, map_mul r' _ c, map_mul _ _ c, hcc, hker (g * c⁻¹) (by simp [h, hc])]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormUniq
section
open Matrix UpperTheory.V.U3

private theorem conj_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ :=
  _root_.UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left h r g

private theorem conj_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) : (conjBy h r g).right = (r g).right :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalTranspose.conj_right h r g

private theorem conj_mat {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) (hg : (r g).right = 1) :
    (conjBy h r g).mat * (h : Matrix (Fin m) (Fin m) R) = (h : Matrix (Fin m) (Fin m) R) * (r g).mat := by
  unfold GG.mat
  rw [conj_left, hg, sgnAct_one, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul]

private theorem unit_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (hb : IsUnit b)
    (h : a - b ∈ IsLocalRing.maximalIdeal R) : IsUnit a := by
  by_contra ha
  have ha' : a ∈ IsLocalRing.maximalIdeal R := ha
  have : b ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ ha' h
  exact this hb

theorem UpperTheory.V.U3.normalised_unique :
    ∀ {G R : Type} [Group G] [CommRing R] [IsLocalRing R]
      (η : G →* ℤˣ) (Ψ : G →* (IsLocalRing.ResidueField R)ˣ) (c g₁ : G) (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R), IsUnit (2 : R) → Marks η Ψ c g₁ →
      (GG.map (IsLocalRing.residue R)).comp r = r0 η Ψ → CongOne (IsLocalRing.maximalIdeal R) h →
      Normalised c g₁ r → Normalised c g₁ (conjBy h r) → ∃ t : Rˣ, (t : R) - 1 ∈ IsLocalRing.maximalIdeal R ∧ h = tor R t := by
  intro G R _ _ _ η Ψ c g₁ r h h2 hM hred hc hN hN'
  have hright : ∀ g, (r g).right = η g := fun g => by
    have := congrArg (fun f : G →* GG (m := 3) (R := IsLocalRing.ResidueField R) => (f g).right) hred
    simpa using this
  have hrc : (r c).right = -1 := (hright c).trans hM.ηc
  have hrg : (r g₁).right = 1 := (hright g₁).trans hM.ηg
  have hrs : (r (gstar c g₁)).right = 1 := by
    rw [hright, gstar, map_mul, map_mul, map_inv, hM.ηc, hM.ηg]; simp
  have hz := zmat_diag r c g₁ h2 hrc hrg hN
  have hz' := zmat_diag (conjBy h r) c g₁ h2 ((conj_right h r c).trans hrc)
    ((conj_right h r g₁).trans hrg) hN'
  have hζ : IsUnit (zeta c g₁ r) := by
    have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ c g₁ hM).2
    rw [← hred] at h1
    have h3 : zeta c g₁ ((GG.map (IsLocalRing.residue R)).comp r) =
        IsLocalRing.residue R (zeta c g₁ r) := by
      simp [zeta, zmat]
    rw [h3] at h1
    exact (isUnit_map_iff _ _).1 h1
  have hcomm : zmat c g₁ (conjBy h r) * (h : Matrix (Fin 3) (Fin 3) R) =
      (h : Matrix (Fin 3) (Fin 3) R) * zmat c g₁ r := by
    rw [zmat, zmat, Matrix.sub_mul, Matrix.mul_sub, conj_mat h r _ hrg, conj_mat h r _ hrs]
  rw [hz, hz'] at hcomm
  generalize zeta c g₁ r = ζ at hζ hcomm
  generalize zeta c g₁ (conjBy h r) = ζ' at hcomm
  have he : ∀ a b, ![ζ', 0, -ζ'] a * h.val a b = h.val a b * ![ζ, 0, -ζ] b := fun a b => by
    have := congrFun (congrFun hcomm a) b
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have hd : ∀ a, h.val a a - 1 ∈ IsLocalRing.maximalIdeal R := fun a => by
    simpa using hc a a
  have hu0 : IsUnit (h.val 0 0) := unit_of_sub_mem isUnit_one (hd 0)
  have hζζ : ζ' = ζ := by
    have := he 0 0
    simp only [Matrix.cons_val_zero] at this
    exact hu0.mul_left_cancel (by rw [← this, mul_comm])
  subst hζζ
  have h2ζ : IsUnit (2 * ζ') := h2.mul hζ
  have e01 : h.val 0 1 = 0 := by
    have := he 0 1
    simp at this
    exact hζ.mul_left_cancel (by simpa using this)
  have e10 : h.val 1 0 = 0 := by
    have := he 1 0
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e12 : h.val 1 2 = 0 := by
    have := he 1 2
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination this)
  have e21 : h.val 2 1 = 0 := by
    have := he 2 1
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e02 : h.val 0 2 = 0 := by
    have := he 0 2
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination this)
  have e20 : h.val 2 0 = 0 := by
    have := he 2 0
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination -this)
  have hθ : theta h⁻¹ = h⁻¹ := by
    have h1 : (r c).left = 1 := Units.ext hN.atc
    have h3 : (conjBy h r c).left = 1 := Units.ext hN'.atc
    rw [conj_left, h1, hrc, sgnAct_neg_one, mul_one] at h3
    exact (eq_inv_of_mul_eq_one_right h3)
  have hJ : h.val * (Jmat R 3 * h.valᵀ * Jmat R 3) = 1 := by
    have := theta_val h⁻¹
    rw [hθ, inv_inv] at this
    rw [← this, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have p0 : h.val 0 0 * h.val 2 2 = 1 := by
    have := congrFun (congrFun hJ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have p1 : h.val 1 1 * h.val 1 1 = 1 := by
    have := congrFun (congrFun hJ 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have e11 : h.val 1 1 = 1 := by
    have hu : IsUnit (h.val 1 1 + 1) :=
      unit_of_sub_mem h2 (by convert hd 1 using 1; ring)
    exact hu.mul_left_cancel (by linear_combination p1)
  refine ⟨Units.mkOfMulEqOne _ _ p0, hd 0, Units.ext ?_⟩
  rw [tor_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wt1, e01, e10, e12, e21, e02, e20, e11, Units.mkOfMulEqOne]
end

