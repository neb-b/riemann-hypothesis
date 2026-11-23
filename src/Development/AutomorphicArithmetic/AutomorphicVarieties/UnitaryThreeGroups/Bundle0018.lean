module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PowEqOneOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtPoints
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ x : c.O, ‖algebraMap c.O (PadicAlgCl l) x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  have h1 : ‖algebraMap c.O (PadicAlgCl l) u‖ * ‖algebraMap c.O (PadicAlgCl l) (u⁻¹ : c.Oˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg (algebraMap c.O (PadicAlgCl l) u)
  nlinarith

private theorem corner_det {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
    (corner X).det = X 0 0 * X 2 2 - X 0 2 * X 2 0 := by
  rw [Matrix.det_fin_two]; rfl

private theorem tor_mat {R : Type} [CommRing R] (p : Rˣ) :
    (tor R p : Matrix (Fin 3) (Fin 3) R) = !![(p : R), 0, 0; 0, 1, 0; 0, 0, ((p⁻¹ : Rˣ) : R)] := by
  rw [tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wt1, Matrix.diagonal]

private theorem eval_block {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) (hc : X.charpoly = (tor k p : Matrix (Fin 3) (Fin 3) k).charpoly) (t : k) :
    (t - X 1 1) * ((t - X 0 0) * (t - X 2 2) - X 0 2 * X 2 0) = (t - p) * (t - 1) * (t - (p⁻¹ : kˣ)) := by
  have := congrArg (Polynomial.eval t) hc
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, tor_mat, Matrix.det_fin_three, Matrix.det_fin_three] at this
  simp [Matrix.scalar_apply, h0, h2] at this
  rw [Units.val_inv_eq_inv_val]
  linear_combination this

private theorem mid_eq_one {k : Type} [NormedField k] [IsUltrametricDist k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (h0 : X 0 1 = 0) (h2 : X 2 1 = 0) (hc : X.charpoly = (tor k p : Matrix (Fin 3) (Fin 3) k).charpoly)
    (h1 : ‖X 1 1 - 1‖ < 1) (hp : ‖(p : k) - 1‖ = 1) (hp' : ‖(p : k)‖ = 1) : X 1 1 = 1 := by
  have := eval_block X p h0 h2 hc (X 1 1)
  rw [sub_self, zero_mul] at this
  rcases mul_eq_zero.1 this.symm with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rw [sub_eq_zero.1 h, hp] at h1
      exact absurd h1 (lt_irrefl _)
    · exact sub_eq_zero.1 h
  · rw [sub_eq_zero.1 h] at h1
    have e : (p : k) * (((p⁻¹ : kˣ) : k) - 1) = -((p : k) - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have e2 := congrArg norm e
    rw [norm_mul, norm_neg, hp, hp', one_mul] at e2
    rw [e2] at h1
    exact absurd h1 (lt_irrefl _)

private theorem det_near {k : Type} [NormedField k] [IsUltrametricDist k] (X : Matrix (Fin 3) (Fin 3) k) (p : kˣ)
    (hi : ∀ a b, ‖X a b‖ ≤ 1) (hr : ∀ a b, ‖X a b - (tor k p : Matrix (Fin 3) (Fin 3) k) a b‖ < 1)
    (hp' : ‖(p : k)‖ = 1) : ‖(corner X).det - 1‖ < 1 := by
  have h00 := hr 0 0
  have h22 := hr 2 2
  have h02 := hr 0 2
  rw [tor_mat] at h00 h22 h02
  change ‖X 0 0 - p‖ < 1 at h00
  change ‖X 2 2 - (p⁻¹ : kˣ)‖ < 1 at h22
  change ‖X 0 2 - 0‖ < 1 at h02
  rw [sub_zero] at h02
  have e : (corner X).det - 1 = ((X 0 0 - p) * X 2 2 + p * (X 2 2 - (p⁻¹ : kˣ))) + -(X 0 2 * X 2 0) := by
    rw [corner_det, mul_sub (p : k), Units.mul_inv]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt
    (lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)) ?_)
  · rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h00 (hi _ _)
  · rw [norm_mul, hp', one_mul]; exact h22
  · rw [norm_neg, norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h02 (hi _ _)

private theorem bar_iff {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] (Ψ : Γ →* Oˣ) (g : Γ) :
    barChar O Ψ g = 1 ↔ ¬ IsUnit ((Ψ g : O) - 1) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one,
    sub_eq_zero, Units.ext_iff]
  rfl

private noncomputable def midChar {G k : Type} [Group G] [Field k] (η : G →* ℤˣ) (r : G →* GG (m := 3) (R := k)) (hm : HasMult η r)
    (hB : Block η r) : η.ker →* kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (r g).mat 1 1
      map_one' := by simp [GG.mat]
      map_mul' := fun g h => by
        have e : (r (g * h : η.ker)).mat = (r g).mat * (r h).mat :=
          congrArg Units.val ((glPart η r hm).map_mul g h)
        rw [e, Matrix.mul_apply, Fin.sum_univ_three, hB g g.2 1 0 (by decide), hB g g.2 1 2 (by decide)]
        ring }

private theorem W_facts {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [NormedField k]
    (η : Γ →* ℤˣ) (r : Γ →* GG (m := 3) (R := k)) (cc : Γ) (hm : HasMult η r) (hc : η cc = -1) (hat : (r cc).mat = 1)
    (hII : TypeII η r) (hb : ∀ g ∈ η.ker, (corner (r g).mat).det = 1) (hct : Continuous (mats r))
    (hηc : IsLocallyConstant η) :
    ∃ W : Γ →* GL (Fin 2) k, (∀ g ∈ η.ker, (W g : Matrix (Fin 2) (Fin 2) k) = corner (r g).mat) ∧
      (W cc : Matrix (Fin 2) (Fin 2) k).trace = 0 ∧ Continuous W ∧ Af.IsIrr W ∧
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) k) = Wfun r g) ∧
      ∀ g, (W g : Matrix (Fin 2) (Fin 2) k).det = ((η g : ℤˣ) : ℤ) := by
  obtain ⟨hB, hirr⟩ := hII
  obtain ⟨W, hW, hWd⟩ := exists_lieElement_middleBlockPart η r cc hm hc hat hB hb
  have hWk : ∀ g ∈ η.ker, (W g : Matrix (Fin 2) (Fin 2) k) = corner (r g).mat := fun g hg => by
    rw [hW, Wfun, if_pos ((hm g).trans hg)]
  have hWc : Continuous fun g => (W g : Matrix (Fin 2) (Fin 2) k) := by
    have e : (fun g => (W g : Matrix (Fin 2) (Fin 2) k)) = fun g => corner (r g).mat *
        (fun s : ℤˣ => if s = 1 then (1 : Matrix (Fin 2) (Fin 2) k) else Matrix.diagonal ![-1, 1]) (η g) := by
      funext g
      rw [hW, Wfun, hm g]
      dsimp only
      split_ifs <;> simp
    rw [e]
    exact (hct.matrix_submatrix _ _).matrix_mul
      (hηc.comp fun s : ℤˣ => if s = 1 then (1 : Matrix (Fin 2) (Fin 2) k) else Matrix.diagonal ![-1, 1]).continuous
  refine ⟨W, hWk, ?_, ?_, ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun V _ hV => hirr V fun g hg v hv => ?_⟩,
    hW, hWd⟩
  · rw [hW, Wfun, if_neg (by rw [hm, hc]; decide), hat]
    rw [Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
    change (1 : k) * (-1) + 1 * 1 = 0
    ring
  · refine Units.continuous_iff.2 ⟨hWc, ?_⟩
    simp only [← map_inv]
    exact hWc.comp continuous_inv
  · have := hV g v hv
    rwa [hWk g hg] at this

theorem UpperTheory.V.U3.typeII_facts :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) ∧ (∀ g ∈ D.η.ker, (corner (r g).mat).det = 1) ∧
        ∃ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W ∧ Continuous W ∧ Af.IsIrr W ∧
          (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = Wfun r g) ∧
          ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hII
  obtain ⟨hB, hirr⟩ := hII
  obtain ⟨-, -, -, hηc, -, -, -, -, -, -, habove⟩ := dat_facts D
  have h0 : ∀ g ∈ D.η.ker, (r g).mat 0 1 = 0 := fun g hg => hB g hg 0 1 (by decide)
  have h2 : ∀ g ∈ D.η.ker, (r g).mat 2 1 = 0 := fun g hg => hB g hg 2 1 (by decide)
  have hΨn : ∀ g, ‖((D.ΨQ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := fun g => norm_unit c (D.Ψ g).isUnit
  have hcp : ∀ (A : ValuationSubring Ω), ∀ g ∈ D.η.ker, g ∈ Ine (F := ℚ) A →
      (r g).mat.charpoly = (tor _ (D.ΨQ g) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).charpoly := by
    intro A g hg hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact (pt_inertia_above hC D hM h A hl).1 g hA
    · obtain ⟨M, hM'⟩ := pt_inertia_away D hM h A hl
      have e1 := hM' g hA hg
      have e2 : (r0 D.η D.ΨQ g).mat = (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat *
          ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
        rw [e1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      change _ = (r0 D.η D.ΨQ g).mat.charpoly
      rw [e2, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hnear : ∀ g, ‖(r g).mat 1 1 - 1‖ < 1 := fun g => by
    have := h.red g 1 1
    change ‖_ - (tor _ (D.ΨQ g) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) 1 1‖ < 1 at this
    rw [tor_mat] at this
    exact this
  have hbar : ∀ g, barChar c.O D.Ψ g = 1 ↔ ¬ IsUnit ((D.Ψ g : c.O) - 1) := bar_iff D.Ψ
  have hfar : ∀ (A : ValuationSubring Ω), ∀ g ∈ D.η.ker, g ∈ Ine (F := ℚ) A → barChar c.O D.Ψ g ≠ 1 →
      (r g).mat 1 1 = 1 := by
    intro A g hg hA hb
    refine mid_eq_one _ _ (h0 g hg) (h2 g hg) (hcp A g hg hA) (hnear g) ?_ (hΨn g)
    have := norm_unit c (not_not.1 fun hn => hb ((hbar g).2 hn))
    rwa [map_sub, map_one] at this
  have hcm : ∀ a b, Continuous fun g => (r g).mat a b := fun a b => h.cont.matrix_elem a b
  have hκ : midChar D.η r h.mult hB = 1 := by
    refine char_eq_one D _ ((hcm 1 1).comp continuous_subtype_val) (fun g => hnear g) fun A g hA => ?_
    by_cases hb : barChar c.O D.Ψ g = 1
    · by_cases hl : A.valuation (l : Ω) < 1
      · obtain ⟨hle, s, hs, hu⟩ := habove A hl
        have hsb : barChar c.O D.Ψ s ≠ 1 := fun hn => (hbar s).1 hn
          (isUnit_of_mul_isUnit_left (y := (D.Ψ s : c.O) + 1) (by convert hu using 1; ring))
        have e1 : midChar D.η r h.mult hB ⟨s, hle hs⟩ = 1 := Units.ext (hfar A s (hle hs) hs hsb)
        have e2 : midChar D.η r h.mult hB (g * ⟨s, hle hs⟩) = 1 :=
          Units.ext (hfar A _ (g * ⟨s, hle hs⟩).2 (mul_mem hA hs) (by
            change barChar c.O D.Ψ (g * s) ≠ 1
            rwa [map_mul, hb, one_mul]))
        rwa [map_mul, e1, mul_one] at e2
      · have hk : (g : G ℚ Ω) ∈ D.Kill := ⟨A, hl, hA, by
          refine SemidirectProduct.ext ?_ g.2
          change tor _ (barChar c.O D.Ψ g) = 1
          rw [hb, map_one]⟩
        refine Units.ext ?_
        change (r g).mat 1 1 = 1
        rw [h.kill g hk]
        simp [GG.mat]
    · exact Units.ext (hfar A g g.2 hA hb)
  have ha : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1 := fun g hg => by
    have := congrArg Units.val (DFunLike.congr_fun hκ (⟨g, hg⟩ : D.η.ker))
    exact this
  have hdet : ∀ g ∈ D.η.ker, (r g).mat.det = (corner (r g).mat).det := fun g hg => by
    rw [corner_det, Matrix.det_fin_three, h0 g hg, h2 g hg, ha g hg]; ring
  have hδ : (Matrix.GeneralLinearGroup.det).comp (glPart D.η r h.mult) = 1 := by
    refine char_eq_one D _ (h.cont.matrix_det.comp continuous_subtype_val) (fun g => ?_) fun A g hA => ?_
    · change ‖(r g).mat.det - 1‖ < 1
      rw [hdet g g.2]
      exact det_near _ _ (h.int g) (h.red g) (hΨn g)
    · refine Units.ext ?_
      change (r g).mat.det = 1
      have := eval_block _ _ (h0 g g.2) (h2 g g.2) (hcp A g g.2 hA) 0
      rw [hdet g g.2, corner_det]
      rw [ha g g.2] at this
      linear_combination (D.ΨQ g).mul_inv - this
  have hb : ∀ g ∈ D.η.ker, (corner (r g).mat).det = 1 := fun g hg => by
    have := congrArg Units.val (DFunLike.congr_fun hδ (⟨g, hg⟩ : D.η.ker))
    exact (hdet g hg).symm.trans this
  obtain ⟨W, H1, H2, H3, H4, H5, H6⟩ := W_facts D.η r D.cc h.mult hM.ηc h.norm.atc ⟨hB, hirr⟩ hb h.cont hηc
  exact ⟨ha, hb, W, ⟨H1, H2⟩, H3, H4, H5, H6⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsFlagCharactersOfUpperTriangular
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem conj_left_block_of_right_one {Γ R : Type} [Group Γ] [CommRing R] (M : GL (Fin 3) R) (r : Γ →* GG (m := 3) (R := R)) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).left = M * (r g).left * M⁻¹ := by
  simp [conjBy, hg]

private theorem conj_left_block_eq_theta {Γ R : Type} [Group Γ] [CommRing R] (r : Γ →* GG (m := 3) (R := R)) (c g : Γ)
    (hc : (r c).mat = 1) (hc' : (r c).right = -1) (hg : (r g).right = 1) : (r (c⁻¹ * g * c)).left = theta (r g).left := by
  have h1 : (r c).left = 1 := Units.ext hc
  have h2 : theta (1 : GL (Fin 3) R) = 1 := map_one (thetaAut 3 R)
  simp [h1, hc', hg, h2]

private theorem exists_flag_characters_of_upper_triangular {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (H : Subgroup Γ) (M : GL (Fin n) k)
    (h : ∀ s ∈ H, ∀ i j, j < i → (M * ρ s * M⁻¹ : GL (Fin n) k) i j = 0) :
    ∃ κ : Fin n → ↥H →* kˣ, Af.IsFlagOn ρ H κ ∧ ∀ i (s : ↥H), (κ i s : k) = (M * ρ s * M⁻¹ : GL (Fin n) k) i i := by
  have hm : ∀ i, ∀ s ∈ H, ∀ t ∈ H, (M * ρ (s * t) * M⁻¹ : GL (Fin n) k) i i =
      (M * ρ s * M⁻¹ : GL (Fin n) k) i i * (M * ρ t * M⁻¹ : GL (Fin n) k) i i := by
    intro i s hs t ht
    have e : M * ρ (s * t) * M⁻¹ = (M * ρ s * M⁻¹) * (M * ρ t * M⁻¹) := by simp [mul_assoc]
    rw [e, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h1 | h1
      · rw [h s hs i j h1, zero_mul]
      · rw [h t ht j i h1, mul_zero]
    · simp
  let κ : Fin n → ↥H →* k := fun i =>
    { toFun := fun s => (M * ρ s * M⁻¹ : GL (Fin n) k) i i
      map_one' := by simp
      map_mul' := fun s t => hm i s s.2 t t.2 }
  exact ⟨fun i => (κ i).toHomUnits, ⟨M, fun s => ⟨h s s.2, fun i => rfl⟩⟩, fun i s => rfl⟩

private theorem crystalline_of_theta_twist_gl3 {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* GQ l) (hφ : Topology.IsOpenEmbedding φ) (E : FinExt l) (ρ : H →* GL (Fin 3) ↥E.1) (hρ : Continuous ρ)
    (h : Loc.IsCr φ (Loc.colRep ρ)) :
    Loc.IsCr φ (Loc.colRep ((thetaAut 3 ↥E.1).toMonoidHom.comp ρ)) := by
  haveI := E.2
  haveI : IsModuleTopology ℚ_[l] ↥E.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] (Fin 3 → ↥E.1) := isModuleTopologyOfFiniteDimensional
  have h0 : Loc.IsCr φ (Loc.chRep (1 : H →* (↥E.1)ˣ)) :=
    Loc.crUnr φ hφ _ (by
      have : ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2 := fun p => by simp [Loc.chRep]
      exact continuous_snd.congr fun p => (this p).symm) 0 fun g _ x => by simp [Loc.chRep]
  have hc : ∀ σ : H →* GL (Fin 3) ↥E.1, Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) ↥E.1)) →
      ContAction (Loc.colRep σ) := fun σ hσ =>
    (hσ.comp continuous_fst).matrix_mulVec continuous_snd
  let b : (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] (Fin 3 → ↥E.1) →ₗ[ℚ_[l]] ↥E.1 :=
    LinearMap.mk₂ ℚ_[l] (fun w x => (Jmat _ 3 *ᵥ w) ⬝ᵥ x) (fun _ _ _ => by simp [Matrix.mulVec_add])
      (fun _ _ _ => by simp [Matrix.mulVec_smul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  refine (Loc.isCrys_isDR_internalHom φ hφ (Loc.colRep ρ) (Loc.chRep (1 : H →* (↥E.1)ˣ)) _ (hc ρ (Units.continuous_val.comp hρ)) ?_
    (hc _ ?_) b (fun g w x => ?_) ?_).1 h h0
  · have : ∀ p : H × ↥E.1, Loc.chRep (1 : H →* (↥E.1)ˣ) p.1 p.2 = p.2 := fun p => by simp [Loc.chRep]
    exact continuous_snd.congr fun p => (this p).symm
  · exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp hρ).matrix_transpose).matrix_mul continuous_const
  · change (Jmat _ 3 *ᵥ ((theta (ρ g) : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ w)) ⬝ᵥ ((ρ g : Matrix (Fin 3) (Fin 3) ↥E.1) *ᵥ x) = (1 : ↥E.1) • ((Jmat _ 3 *ᵥ w) ⬝ᵥ x)
    rw [one_smul, theta_val, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec]
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : Jmat _ 3 *ᵥ w = 0 := dotProduct_eq_zero _ fun x => LinearMap.congr_fun hw x
    have h2 := congrArg (Jmat _ 3 *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, Jmat_mul_Jmat] using h2

private theorem continuous_of_matrix_units {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing k] [TopologicalSpace k]
    {n : ℕ} (ρ : Γ →* GL (Fin n) k) (h : Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) k)) : Continuous ρ :=
  Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]⟩

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
  {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω} {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)}

private theorem isAlgClosure_of_number_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem continuous_rho_of_point (h : D.IsPt U g₁ r) : Continuous (D.rhoK r h.mult) := by
  haveI := isAlgClosure_of_number_field Ω K
  exact continuous_of_matrix_units _ (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)

private theorem exists_local_crystalline_gl3_model (hI : CohInp) (h : D.IsPt U g₁ r) :
    ∃ (E : FinExt l) (ρ : ↥D.loc.HL →* GL (Fin 3) ↥E.1),
      (∀ g, GeneralLinearGroup.map (E.1.val : ↥E.1 →+* PadicAlgCl l) (ρ g) = (r (D.ι g)).left) ∧
      Loc.IsCr D.loc.HL.subtype (Loc.colRep ρ) := by
  obtain ⟨f, hf, hker, hpush⟩ := h.loc
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (dvrFacts l c.O).2.2.2.1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) U.R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  letI : Algebra c.O ↥E.1 := ((algebraMap c.O (PadicAlgCl l)).codRestrict E.1 fun a => f.commutes a ▸ hE' _).toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O ↥E.1 := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  let f' : U.R →ₐ[c.O] ↥E.1 :=
    { (f : U.R →+* PadicAlgCl l).codRestrict E.1 hE' with commutes' := fun a => Subtype.ext (f.commutes a) }
  obtain ⟨-, -, ρ, h1, h2⟩ := Loc.rtPoints hI.loc D.loc U ↥E.1 (push f' U.r.hom)
    ⟨f', rfl, fun a ha => Subtype.ext (hker ha)⟩
  refine ⟨E, ρ, fun g => ?_, h2⟩
  rw [h1, ← MonoidHom.comp_apply r D.ι, ← hpush]
  rfl

private theorem potentially_crystalline_conjugate_place (hI : CohInp) (h : D.IsPt U g₁ r) (g : G ℚ Ω) (hg : g = 1 ∨ g = D.cc) :
    Af.PotCrysAt (D.rhoK r h.mult) (Loc.placeJ (D.j.comp (g : Ω →+* Ω))) := by
  haveI := isAlgClosure_of_number_field Ω K
  obtain ⟨E, ρ, h1, h2⟩ := exists_local_crystalline_gl3_model D hI h
  obtain ⟨-, hcc, -, hη, -⟩ := dat_facts D
  have hop : IsOpen (D.loc.HL : Set (GQ l)) :=
    ((hη.comp_continuous D.ι_cont).isOpen_fiber 1).inter D.τ_open
  have hφ : Topology.IsOpenEmbedding D.loc.HL.subtype := hop.isOpenEmbedding_subtypeVal
  have hinj := (galEmbTop ℚ K Ω).1.injective
  have hη1 : ∀ s : ↥D.loc.HL, D.η (D.ι s) = 1 := fun s => s.2.1
  let ψ₀ : ↥D.loc.HL →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (D.ι.comp D.loc.HL.subtype)
  have hψ₀ : ∀ s, ψ₀ s = g⁻¹ * D.ι s * g := fun s => by simp [ψ₀]
  have hmem : ∀ s, ψ₀ s ∈ (galEmb ℚ K Ω).range := fun s => by
    rw [range_galEmb, ← D.η_ker, MonoidHom.mem_ker, hψ₀]
    simp [hη1]
  let ψ' : ↥D.loc.HL →* G K Ω := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ψ₀.codRestrict _ hmem)
  have hψ' : ∀ s, galEmb ℚ K Ω (ψ' s) = g⁻¹ * D.ι s * g := fun s =>
    (MonoidHom.apply_ofInjective_symm hinj _).trans (hψ₀ s)
  have hspec : ∀ (s : ↥D.loc.HL) (y : Ω), D.loc.HL.subtype s ((D.j.comp (g : Ω →+* Ω)) y) = (D.j.comp (g : Ω →+* Ω)) (ψ' s y) := by
    intro s y
    change (s : GQ l) (D.j (g y)) = D.j (g (galEmb ℚ K Ω (ψ' s) y))
    rw [D.ι_spec, hψ']
    simp
  have hρ : Continuous ρ := by
    refine continuous_of_matrix_units _ (continuous_pi fun a => continuous_pi fun b => continuous_induced_rng.2 ?_)
    have h3 : Continuous fun s : ↥D.loc.HL => (r (D.ι s)).mat a b :=
      (h.cont.comp (D.ι_cont.comp continuous_subtype_val)).matrix_elem a b
    exact h3.congr fun s => by rw [GG.mat, ← h1]; rfl
  rcases hg with rfl | rfl
  · refine Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E ρ (fun s a b => ?_) h2
    rw [Dat.rhoK_apply, hψ', inv_one, one_mul, mul_one, ← h1]
    rfl
  · refine Loc.potCrysOf _ _ ψ' hφ hspec _ (continuous_rho_of_point D h) E _ (fun s a b => ?_) (crystalline_of_theta_twist_gl3 _ hφ E ρ hρ h2)
    rw [Dat.rhoK_apply, hψ', conj_left_block_eq_theta r _ _ h.norm.atc ((h.mult _).trans hcc) ((h.mult _).trans (hη1 s)), ← h1,
      ← map_theta]
    rfl

private theorem exists_place_over_conjugate_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    ∃ g : G ℚ Ω, (g = 1 ∨ g = D.cc) ∧ IsPlaceOver (Loc.placeJ (D.j.comp (g : Ω →+* Ω))) w := by
  haveI := isAlgClosure_of_number_field Ω K
  obtain ⟨-, hcc, -⟩ := dat_facts D
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := K) (Ω := Ω) (v := l)).1 _ w (isPlaceOver_placeOf Ω w) hw
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, ∀ x, j x = D.j (g x) := by
    letI : Algebra Ω (Om l) := D.j.toAlgebra
    haveI : IsScalarTower ℚ Ω (Om l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact ⟨AlgHom.restrictNormal' j.toRatAlgHom Ω, fun x => (AlgHom.restrictNormal_commutes j.toRatAlgHom Ω x).symm⟩
  have key : ∀ g' : G ℚ Ω, D.η g' = D.η g → IsPlaceOver (Loc.placeJ (D.j.comp (g' : Ω →+* Ω))) w := by
    intro g' hg' x
    have h1 : g'⁻¹ * g ∈ (galEmb ℚ K Ω).range := by
      rw [range_galEmb, ← D.η_ker, MonoidHom.mem_ker]
      simp [hg']
    obtain ⟨k, hk⟩ := h1
    have h2 : ∀ y : K, (D.j.comp (g' : Ω →+* Ω)) (algebraMap K Ω y) = j (algebraMap K Ω y) := fun y => by
      rw [hg, ← mul_inv_cancel_left g' g, ← hk, AlgEquiv.mul_apply, galEmb_apply, AlgEquiv.commutes]
      rfl
    rw [← isPlaceOver_placeOf Ω w x, ← hj, ← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀]
    simp only [Loc.placeJ, ValuationSubring.mem_comap, h2]
  rcases Int.units_eq_one_or (D.η g) with h1 | h1
  · exact ⟨1, Or.inl rfl, key _ (by rw [h1, map_one])⟩
  · exact ⟨_, Or.inr rfl, key _ (by rw [h1, hcc])⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TypeIIrrCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem twist_triv {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    (D : Dat Ω K c e ψ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {C : Type} [Group C]
    (φ : G K Ω →* C) (hφ : (cycBar K Ω l).ker ≤ φ.ker) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A → φ s ≠ 1 → D.ΨQ (galEmb ℚ K Ω s) ^ m = 1) (g : G K Ω) :
    φ g = 1 := by
  have hl : l.Prime := Fact.out
  have hI : Ine (F := ℚ) A ≤ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = u := fun u => by
    obtain ⟨σ, hσ, hu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
    obtain ⟨s, rfl⟩ := hI hσ
    exact ⟨s, hσ, hu⟩
  by_contra hg
  obtain ⟨s, hs, hsg⟩ := hsur (cycZ K Ω l g)
  have hs1 : φ s ≠ 1 := by
    intro h1
    have : φ (g * s⁻¹) = 1 := hφ (by
      rw [MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])
    rw [map_mul, map_inv, h1, inv_one, mul_one] at this
    exact hg this
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, ht, htu⟩ := hsur hu.unit
  have ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1 := by
    by_cases h1 : φ t = 1
    · have h2 := h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])
      rwa [map_mul, map_mul, mul_pow, h s hs hs1, one_mul] at h2
    · exact h t ht h1
  have hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O) := by
    have : cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit := htu
    rw [chiO, MonoidHom.comp_apply, this]
    simp
  have h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ) := by
    rw [Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul,
      Units.val_pow_eq_pow_val, hc]
  have h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ) := by
    have := congrArg (algebraMap c.O (PadicAlgCl l)) h3
    rw [map_pow, map_natCast] at this
    rw [← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]
    rfl
  have h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by
    rw [pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]
  have h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by exact_mod_cast h5
  have he := D.gd.e_pos
  have hN : 0 < Nat.card (ZMod N)ˣ := Nat.card_pos
  rcases Nat.pow_eq_one.1 h6 with h7 | h7
  · exact hl.ne_zero (by omega)
  · exact (mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7
end

