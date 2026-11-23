module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardUnipotentUpperEqPow
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.V.T.UnipCard

private def upMat (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

private theorem upMat_lower (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i j : Fin n) (h : j < i) :
    upMat R n f i j = 0 := by
  simp [upMat, not_lt.2 h.le, h.ne']

private theorem upMat_diag (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i : Fin n) :
    upMat R n f i i = 1 := by
  simp [upMat]

private theorem upMat_det (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : (upMat R n f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => upMat_lower R n f i j h)]
  simp [upMat_diag]

private noncomputable def upGL (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R :=
  Matrix.nonsingInvUnit (upMat R n f) (by rw [upMat_det]; exact isUnit_one)

private theorem upGL_val (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (upGL R n f : Matrix (Fin n) (Fin n) R) = upMat R n f := rfl

private noncomputable def unipEquiv (R : Type) [CommRing R] (n : ℕ) :
    unipB R (Fin n) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun g := fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
  invFun f := ⟨upGL R n f, (mem_unipB R).2 ⟨fun i j h => by
      rw [upGL_val]; exact upMat_lower R n f i j h, fun i => by
      rw [upGL_val]; exact upMat_diag R n f i⟩⟩
  left_inv g := by
    obtain ⟨hl, hd⟩ := (mem_unipB R).1 g.2
    apply Subtype.ext
    apply Units.ext
    funext i j
    show ((upGL R n (fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) : GL (Fin n) R) :
      Matrix (Fin n) (Fin n) R) i j = _
    rw [upGL_val]
    rcases lt_trichotomy i j with h | h | h
    · simp [upMat, h]
    · subst h
      simp [upMat, hd]
    · have h1 : ¬ i < j := not_lt.2 h.le
      have h2 : i ≠ j := h.ne'
      simp [upMat, h1, h2, hl i j h]
  right_inv f := by
    funext p
    show upMat R n f p.1.1 p.1.2 = f p
    have h : p.1.1 < p.1.2 := p.2
    simp [upMat, h]

end UpperTheory.V.T.UnipCard

theorem UpperTheory.card_unipotent_upper_eq_pow :
    ∀ (R : Type) [CommRing R] [Finite R] (n : ℕ), ∃ j : ℕ, Nat.card (unipB R (Fin n)) = Nat.card R ^ j := by
  intro R _ _ n
  refine ⟨Nat.card {p : Fin n × Fin n // p.1 < p.2}, ?_⟩
  rw [Nat.card_congr (UpperTheory.V.T.UnipCard.unipEquiv R n), Nat.card_fun]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsInjectiveGenericUnipotentCharacters
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.UnipChar

variable {F : Type} [Field F] {n : ℕ}

private abbrev SD (n : ℕ) := {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1}

private theorem SD.ne (p : SD n) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp := p.2
  rw [h] at hp
  omega

private theorem super_mul {x y : Matrix (Fin n) (Fin n) F}
    (hx : ∀ i j, j < i → x i j = 0) (hx1 : ∀ i, x i i = 1)
    (hy : ∀ i j, j < i → y i j = 0) (hy1 : ∀ i, y i i = 1)
    {i j : Fin n} (h : (j : ℕ) = i + 1) : (x * y) i j = x i j + y i j := by
  rw [Matrix.mul_apply]
  have hij : i ≠ j := by
    intro e
    rw [e] at h
    omega
  rw [Fintype.sum_eq_add i j hij]
  · rw [hx1, hy1, one_mul, mul_one, add_comm]
  · rintro k ⟨hki, hkj⟩
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hx i k hk, zero_mul]
    · have h1 := Fin.lt_iff_val_lt_val.mp hk
      have h2 : (k : ℕ) ≠ j := fun e => hkj (Fin.ext e)
      have hjk : j < k := Fin.lt_iff_val_lt_val.mpr (by omega)
      rw [hy k j hjk, mul_zero]

private def sup (f : SD n → Fˣ) (x : Matrix (Fin n) (Fin n) F) : F :=
  ∑ p, (f p : F) * x p.1.1 p.1.2

private theorem sup_one (f : SD n → Fˣ) : sup f (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  unfold sup
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.one_apply_ne (SD.ne p), mul_zero]

private theorem sup_mul (f : SD n → Fˣ) {x y : GL (Fin n) F}
    (hx : x ∈ unipB F (Fin n)) (hy : y ∈ unipB F (Fin n)) :
    sup f ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      sup f (x : Matrix (Fin n) (Fin n) F) + sup f (y : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨a, b⟩ := (mem_unipB F).1 hx
  obtain ⟨c, d⟩ := (mem_unipB F).1 hy
  unfold sup
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.val_mul, super_mul a b c d p.2, mul_add]

private noncomputable def chi (φ : AddChar F Circle) (f : SD n → Fˣ) : unipB F (Fin n) →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ)
      map_one' := by simp [sup_one]
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, sup_mul f x.2 y.2, AddChar.map_add_eq_mul, Circle.coe_mul] }

private theorem chi_apply (φ : AddChar F Circle) (f : SD n → Fˣ) (x : unipB F (Fin n)) :
    ((chi φ f x : ℂˣ) : ℂ) = (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ) := rfl

private noncomputable def tv (i j : Fin n) (h : i ≠ j) (c : F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

private theorem tv_apply (i j : Fin n) (h : i ≠ j) (c : F) (a b : Fin n) :
    ((tv i j h c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      (1 : Matrix (Fin n) (Fin n) F) a b + Matrix.single i j c a b := rfl

private theorem tv_mem (p : SD n) (c : F) : tv p.1.1 p.1.2 (SD.ne p) c ∈ unipB F (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [tv_apply, Matrix.one_apply_ne (ne_of_gt hab), Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    have h1 := p.2
    have h2 := Fin.lt_iff_val_lt_val.mp hab
    omega
  · rw [tv_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    exact SD.ne p h.symm

private theorem sup_tv (f : SD n → Fˣ) (p : SD n) (c : F) :
    sup f ((tv p.1.1 p.1.2 (SD.ne p) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = f p * c := by
  simp only [sup]
  rw [Finset.sum_eq_single p]
  · rw [tv_apply, Matrix.one_apply_ne (SD.ne p), zero_add, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro q _ hq
    rw [tv_apply, Matrix.one_apply_ne (SD.ne q), zero_add, Matrix.single_apply, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    exact hq (Subtype.ext (Prod.ext h1.symm h2.symm))
  · intro h
    exact absurd (Finset.mem_univ p) h

private theorem chi_inj (φ : AddChar F Circle) (hφ : φ ≠ 1) :
    Function.Injective (chi (n := n) φ) := by
  intro f g hfg
  funext p
  by_contra hne
  apply hφ
  ext a
  have hd : ((f p : F) - g p) ≠ 0 := sub_ne_zero.mpr (fun e => hne (Units.ext e))
  have key := congrArg (fun χ => ((χ ⟨tv p.1.1 p.1.2 (SD.ne p) (((f p : F) - g p)⁻¹ * a), tv_mem p _⟩ : ℂˣ) : ℂ)) hfg
  simp only [chi_apply, sup_tv] at key
  have key' : φ ((f p : F) * (((f p : F) - g p)⁻¹ * a)) = φ ((g p : F) * (((f p : F) - g p)⁻¹ * a)) :=
    Circle.coe_injective key
  have ha : a = (f p : F) * (((f p : F) - g p)⁻¹ * a) - g p * (((f p : F) - g p)⁻¹ * a) := by
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [AddChar.one_apply, ha, AddChar.map_sub_eq_div, key', div_self']

private noncomputable def psi (φ : AddChar F Circle) : AddChar F ℂ where
  toFun a := (φ a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_prim {φ : AddChar F Circle} (hφ : φ ≠ 1) : (psi φ).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h
  apply hφ
  ext a
  have e := congrArg (fun ψ : AddChar F ℂ => ψ a) h
  simp only [AddChar.one_apply] at e ⊢
  exact e.trans Circle.coe_one.symm

private theorem sum_units_eq [Fintype F] [DecidableEq F] (h : F → ℂ) :
    ∑ a : Fˣ, h a = ∑ a : F, h a - h 0 := by
  rw [← Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    Finset.sum_subtype (Finset.univ.erase 0) (p := fun a => a ≠ 0) (fun a => by simp)]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

private theorem sum_units_psi [Fintype F] [DecidableEq F] {φ : AddChar F Circle} (hφ : φ ≠ 1) (b : F) :
    ∑ a : Fˣ, psi φ (-((a : F) * b)) =
      (((Fintype.card F : ℤ) * (if b = 0 then 1 else 0) - 1 : ℤ) : ℂ) := by
  rw [sum_units_eq (fun a : F => psi φ (-(a * b)))]
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, ← mul_neg]
  rw [AddChar.sum_mulShift (-b) (psi_prim hφ)]
  by_cases hb : b = 0 <;> simp [hb]

private theorem psi_sum {ι : Type} (φ : AddChar F Circle) (s : Finset ι) (g : ι → F) :
    psi φ (∑ i ∈ s, g i) = ∏ i ∈ s, psi φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

private theorem chi_inv [Fintype F] [DecidableEq F] (φ : AddChar F Circle) (f : SD n → Fˣ)
    (x : unipB F (Fin n)) :
    (((chi φ f x)⁻¹ : ℂˣ) : ℂ) =
      ∏ p, psi φ (-((f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2)) := by
  rw [Units.val_inv_eq_inv_val, chi_apply, ← psi_sum, Finset.sum_neg_distrib]
  simp only [sup]
  show _ = ((φ (-_) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv]

end UpperTheory.UnipChar

open UpperTheory.UnipChar in
theorem UpperTheory.exists_injective_generic_unipotent_characters :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (φ : AddChar F Circle), φ ≠ 1 →
        ∃ χ : ({p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1} → Fˣ) → (unipB F (Fin n) →* ℂˣ),
          Function.Injective χ ∧
          (∀ f x, ((χ f x : ℂˣ) : ℂ) = (φ (∑ p, (f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) : ℂ)) ∧
          ∃ c : unipB F (Fin n) → ℤ, ∀ x, (c x : ℂ) = ∑ f, (((χ f x)⁻¹ : ℂˣ) : ℂ) := by
  intro F _ _ _ n φ hφ
  refine ⟨chi φ, chi_inj φ hφ, fun f x => chi_apply φ f x, ?_⟩
  refine ⟨fun x => ∏ p : SD n, ((Fintype.card F : ℤ) *
    (if ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = 0 then 1 else 0) - 1), fun x => ?_⟩
  simp only [Int.cast_prod, chi_inv]
  refine Eq.trans ?_ (Fintype.prod_sum (κ := fun _ : SD n => Fˣ)
    (fun p (a : Fˣ) => psi φ (-((a : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2))))
  exact Finset.prod_congr rfl fun p _ => (sum_units_psi hφ _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLevelOneAddCharLiftingResidue
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem sep_char {A : Type} [AddCommGroup A] (H : AddSubgroup A) {a : A} (ha : a ∉ H) :
    ∃ ψ : AddChar A Circle, (∀ u ∈ H, ψ u = 1) ∧ ψ a ≠ 1 := by
  have hne : (a : A ⧸ H) ≠ 0 := fun h => ha ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let e : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨m, rfl⟩
      exact ⟨m, by simp⟩)
  have he : ∀ b, e b = 0 → b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H q =>
      intro h
      have h1 : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
      rw [AddCircle.coe_eq_zero_iff] at h1 ⊢
      obtain ⟨m, hm⟩ := h1
      refine ⟨m, ?_⟩
      have h2 : ((m : ℚ) : ℝ) = q := by simpa using hm
      have h3 : (m : ℚ) = q := by exact_mod_cast h2
      simpa using h3
  let f : A →+ AddCircle (1 : ℝ) := e.comp (AddMonoidHom.comp (χ : A ⧸ H →+ AddCircle (1 : ℚ)) (QuotientAddGroup.mk' H))
  let ψ : AddChar A Circle :=
    { toFun := fun x => AddCircle.toCircle (f x)
      map_zero_eq_one' := by rw [map_zero, AddCircle.toCircle_zero]
      map_add_eq_mul' := fun x y => by rw [map_add (f := _), AddCircle.toCircle_add] }
  refine ⟨ψ, fun u hu => ?_, fun h => ?_⟩
  · have h0 : f u = 0 := by
      have : QuotientAddGroup.mk' H u = 0 := (QuotientAddGroup.eq_zero_iff _).2 hu
      show e (χ (QuotientAddGroup.mk' H u)) = 0
      rw [this, map_zero, map_zero]
    show AddCircle.toCircle (f u) = 1
    rw [h0, AddCircle.toCircle_zero]
  · have h2 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h
    exact hχ (he _ (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h2))

private theorem cont_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (H : AddSubgroup A) (hH : IsOpen (H : Set A)) (ψ : AddChar A Circle) (h : ∀ u ∈ H, ψ u = 1) :
    Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' (H : Set A), hH.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · simp [H.zero_mem]
  · intro y hy
    have h1 : ψ (y - x) = 1 := h _ hy
    have h2 : y = (y - x) + x := by abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]

theorem UpperTheory.exists_level_one_addChar_lifting_residue :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
        ∃ (ψ : AddChar k Circle) (φ : AddChar 𝓀[k] Circle), Lev1 ψ ∧ φ ≠ 1 ∧ ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := by
  intro k _ _ _ _
  let M : AddSubgroup k :=
    { carrier := {x | valuation k x < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt ((valuation k).map_add a b) (max_lt ha hb)
      neg_mem' := fun {a} ha => by
        show valuation k (-a) < 1
        rw [Valuation.map_neg]; exact ha }
  have hMo : IsOpen (M : Set k) := by
    have h := Valuation.isOpen_ball (v := valuation k) 1
    convert h using 1
    ext x
    exact ((valuation k).restrict_lt_one_iff (x := x)).symm
  have h1M : (1 : k) ∉ M := by
    intro h
    have h' : valuation k (1 : k) < 1 := h
    simp at h'
  obtain ⟨ψ, hψM, hψ1⟩ := sep_char M h1M
  have hres : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z → ψ (y : k) = ψ (z : k) := by
    intro y z h
    have h0 : IsLocalRing.residue 𝒪[k] (y - z) = 0 := by rw [map_sub, h, sub_self]
    have h1 : ψ ((y - z : 𝒪[k]) : k) = 1 := hψM _ ((GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 h0)
    have h2 : (y : k) = ((y - z : 𝒪[k]) : k) + (z : k) := by push_cast; abel
    rw [h2, AddChar.map_add_eq_mul, h1, one_mul]
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  let σ : 𝓀[k] → 𝒪[k] := Function.surjInv hsurj
  have hσ : ∀ c, IsLocalRing.residue 𝒪[k] (σ c) = c := Function.surjInv_eq hsurj
  let φ : AddChar 𝓀[k] Circle :=
    { toFun := fun c => ψ (σ c : k)
      map_zero_eq_one' := by
        have : ψ (σ 0 : k) = ψ ((0 : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_zero])
        rw [this]; simp
      map_add_eq_mul' := fun c d => by
        have : ψ (σ (c + d) : k) = ψ ((σ c + σ d : 𝒪[k]) : k) := hres _ _ (by rw [hσ, map_add (f := _), hσ, hσ])
        rw [this]; push_cast; rw [AddChar.map_add_eq_mul] }
  have hφ : ∀ y : 𝒪[k], ψ (y : k) = φ (IsLocalRing.residue 𝒪[k] y) := fun y =>
    hres _ _ (hσ _).symm
  refine ⟨ψ, φ, ⟨cont_char M hMo ψ hψM, hψM, 1, by simp, hψ1⟩, fun h => hψ1 ?_, hφ⟩
  have h2 := hφ 1
  rw [h] at h2
  simpa using h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNonzeroFormFixedByLevelOfUnramified
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem locU_congr {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    (h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) {x : UA L n} (hx : x ∈ locU n w) : x ∈ locU n u := by
  unfold locU at hx ⊢
  rw [h]
  exact hx

private theorem local_retraction_component_cases {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n) :
    cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = cLoc u x ∨ cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = 1 := by
  by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · exact Or.inl (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq h x)
  · exact Or.inr (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne h x)

private theorem local_retraction_mem_comap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n)
    {H : Subgroup (GL (Fin n) (u.adicCompletion L))} (hx : cLoc u x ∈ H) : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) ∈ H := by
  rcases local_retraction_component_cases w u x with h | h <;> rw [h]
  · exact hx
  · exact one_mem _

private theorem local_retraction_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n)
    (hx : cLoc u x = 1) : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = 1 :=
  (local_retraction_component_cases w u x).elim (fun h => h.trans hx) id

private theorem ne_zero_of_irr {G H W M : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (p : G →* H) (hp : Function.Surjective p) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible) (R : G → M →ₗ[ℂ] M)
    (f : W →ₗ[ℂ] M) (hf : f ≠ 0) (he : ∀ x v, f (ρ (p x) v) = R x (f v)) {v : W} (hv : v ≠ 0) : f v ≠ 0 := by
  intro h0
  let S : Subrepresentation ρ := ⟨LinearMap.ker f, fun g y hy => by
    obtain ⟨x, rfl⟩ := hp g
    rw [LinearMap.mem_ker] at hy ⊢
    rw [he, hy, map_zero]⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hv (by simpa [h1] using (LinearMap.mem_ker.2 h0))
  · have h1 : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact hf (LinearMap.ker_eq_top.1 h1)

theorem UpperTheory.exists_nonzero_form_fixed_by_level_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (σ : Submodule ℂ (UA L n → ℂ)), IsAutRepU σ → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n), (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ V.S' → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) → cLoc (s.w s.v0) k ∈ Kc _ n 1 → (∀ v : V.frame.Vl, cLoc (s.w v.1) k = 1) → (∀ u : s.St, cLoc (s.w u) k = 1) → (∀ q : Q.Q, cLoc (Q.wq q) k = 1) → RU L n k φ = φ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q σ hσ hun hτ
  obtain ⟨hund, hspl⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hsplit : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw => hspl w (V.split _ hw)
  let K : Subgroup (UA L n) :=
    { carrier := {k | k ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n) ∧
        (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ V.S' → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) ∧
        cLoc (s.w s.v0) k ∈ Kc _ n 1 ∧ (∀ v : V.frame.Vl, cLoc (s.w v.1) k = 1) ∧ (∀ u : s.St, cLoc (s.w u) k = 1) ∧
        (∀ q : Q.Q, cLoc (Q.wq q) k = 1)}
      one_mem' := ⟨one_mem _, fun u _ => by rw [map_one]; exact one_mem _, by rw [map_one]; exact one_mem _,
        fun _ => map_one _, fun _ => map_one _, fun _ => map_one _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1,
        fun u hu => by rw [map_mul]; exact mul_mem (ha.2.1 u hu) (hb.2.1 u hu),
        by rw [map_mul]; exact mul_mem ha.2.2.1 hb.2.2.1,
        fun v => by rw [map_mul, ha.2.2.2.1 v, hb.2.2.2.1 v, one_mul],
        fun v => by rw [map_mul, ha.2.2.2.2.1 v, hb.2.2.2.2.1 v, one_mul],
        fun v => by rw [map_mul, ha.2.2.2.2.2 v, hb.2.2.2.2.2 v, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1,
        fun u hu => by rw [map_inv]; exact inv_mem (ha.2.1 u hu),
        by rw [map_inv]; exact inv_mem ha.2.2.1,
        fun v => by rw [map_inv, ha.2.2.2.1 v, inv_one],
        fun v => by rw [map_inv, ha.2.2.2.2.1 v, inv_one],
        fun v => by rw [map_inv, ha.2.2.2.2.2 v, inv_one]⟩ }
  have hKO : ∀ u : Plc L, KO (u.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL u (n := n) :=
    fun u => GlobalTheory.SmGL.SphCompletion.KO_completion u n
  have hT : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite := by
    refine V.fin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have key := UpperTheory.exists_fixed_vector_of_local_fixed_vectors L n σ hσ K (fun k hk => hk.1)
    (fun w k hk => ⟨(Subgroup.mem_inf.1 (GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k)).1,
      fun u hu => local_retraction_mem_comap w u k (hk.2.1 u hu), local_retraction_mem_comap w _ k hk.2.2.1,
      fun v => local_retraction_eq_one w _ k (hk.2.2.2.1 v), fun v => local_retraction_eq_one w _ k (hk.2.2.2.2.1 v),
      fun v => local_retraction_eq_one w _ k (hk.2.2.2.2.2 v)⟩) _ hT
    (fun k hk u hu => hKO u ▸ hk.2.1 u hu) ?_
  · obtain ⟨φ, h1, h2, h3⟩ := key
    exact ⟨φ, h1, h2, fun k a b c d e f => h3 k ⟨a, b, c, d, e, f⟩⟩
  intro w
  have htriv : ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → w.under (𝓞 (Lp L)) ∈ V.S' →
      (∀ k ∈ K, cLoc u k = 1) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU L n k φ = φ := by
    intro u hu hw h1
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    refine ⟨φ, hφ, h0, fun k hk hl => ?_⟩
    have h2 : k = 1 := congrArg Subtype.val
      (GlobalTheory.SplitPts.eq_one_of_cLoc (hsplit u (hu ▸ hw)) ⟨k, locU_congr hu hl⟩ (h1 k hk))
    rw [h2, map_one]
    rfl
  by_cases hw : w.under (𝓞 (Lp L)) ∈ V.S'
  · have hw' := hw
    rw [Q.range] at hw'
    rcases hw' with (h | h | h) | ⟨q, h⟩
    · exact htriv (s.w _) (hund _) hw fun k hk => hk.2.2.2.1 ⟨_, h⟩
    · exact htriv (s.w _) (hund _) hw fun k hk => hk.2.2.2.2.1 ⟨_, h⟩
    · obtain ⟨τ, ⟨hirr, f, hf, hfσ, he⟩, hfix⟩ := hτ
      have hu : (s.w s.v0).under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := (hund _).trans h.symm
      obtain ⟨⟨j, hj1, hj2, -⟩, -⟩ := UpperTheory.V.Hi.secU l L Ω s n hn (s.w s.v0) (hsplit _ (hu ▸ hw))
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
      refine ⟨f v, hfσ v, ne_zero_of_irr _ (fun g => ⟨⟨j g, hj1 g⟩, hj2 g⟩) τ.ρ hirr
        (fun x => RU L n (x : locU n (s.w s.v0))) f hf he hv0, fun k hk hl => ?_⟩
      rw [← he ⟨k, locU_congr hu hl⟩ v]
      exact congrArg f (hv _ hk.2.2.1)
    · exact htriv (Q.wq q) h hw fun k hk => hk.2.2.2.2.2 q
  · obtain ⟨φ, h1, h2, h3⟩ := hun w hw
    exact ⟨φ, h1, h2, fun k hk hl => h3 k hl (hKO w ▸ hk.2.1 w hw)⟩
end

