module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  have h1 := Chr.cls_spec (k := ℚ) N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ 1 = ζ ^ ((Chr.cls ℚ Ω N g : ZMod N)).val := by rw [pow_one]; exact h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h2
  ext
  rw [Units.val_one]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at this
  exact this.symm

private theorem block_form {k : Type} [Field k] (X : Matrix (Fin 3) (Fin 3) k) (Y : Matrix (Fin 2) (Fin 2) k)
    (hb : ∀ a b, Odd (wt a b) → X a b = 0) (h1 : X 1 1 = 1) (hY : Y = corner X) :
    X = !![Y 0 0, 0, Y 0 1; 0, 1, 0; Y 1 0, 0, Y 1 1] := by
  subst hY
  have e01 := hb 0 1 (by decide)
  have e10 := hb 1 0 (by decide)
  have e12 := hb 1 2 (by decide)
  have e21 := hb 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, e01, e10, e12, e21, h1]

private theorem conj_mat {Γ k : Type} [Group Γ] [Field k] (M : GL (Fin 3) k) (r : Γ →* GG (m := 3) (R := k)) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).mat = (M : Matrix (Fin 3) (Fin 3) k) * (r g).mat * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have e : (conjBy M r g) = GG.ofGL M * r g * (GG.ofGL M)⁻¹ := rfl
  rw [e, GG.mat, ← map_inv]
  simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, hg, GG.mat, Units.val_mul]

private theorem eigvec {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 → ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) =
      a • (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  set A := (M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) with hA
  set Mi := ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  have hMi : Mi * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    simp [Mi]
  have hXM : X * Mi = Mi * A := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMi, Matrix.one_mul]
  have hcol : A *ᵥ Pi.single 0 1 = a • Pi.single 0 1 := by
    have h10 : A 1 0 = 0 := h 1 0 (by simp [wt, wt1])
    have h20 : A 2 0 = 0 := h 2 0 (by simp [wt, wt1])
    ext i
    fin_cases i <;> simp [Matrix.mulVec_single, h0, h10, h20]
  rw [Matrix.mulVec_mulVec, hXM, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul]

private theorem exists_two {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
  have hnd : ¬ ((l : ℤ) ∣ 2) := by
    intro hd
    have := Int.le_of_dvd (by norm_num) hd
    have hle : l ≤ 2 := by exact_mod_cast this
    have := hl.out.two_le
    omega
  have hu : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    have a1 := PadicInt.norm_le_one (2 : ℤ_[l])
    have a2 : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hnd
    push_cast at a2
    exact le_antisymm a1 (not_lt.mp a2)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun n hn => ?_⟩
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hpow : hu.unit ^ n = 1 := by
    apply Units.map_injective (f := ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) hinj
    rw [map_zpow, map_one, ← hsv]
    exact hn
  have hq : ((2 : ℚ) : ℚ_[l]) ^ n = 1 := by
    have := congrArg (fun x : ℤ_[l]ˣ => ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom x : ℚ_[l]ˣ) : ℚ_[l])) hpow
    simp only [map_zpow, map_one, Units.val_one, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec] at this
    have e : (PadicInt.Coe.ringHom (p := l)) (2 : ℤ_[l]) = 2 := map_ofNat _ 2
    change (PadicInt.Coe.ringHom (p := l)) 2 ^ n = 1 at this
    rw [e] at this
    simpa using this
  have hq' : (2 : ℚ) ^ n = 1 := by
    have := hq
    rw [← Rat.cast_zpow, ← Rat.cast_one] at this
    exact_mod_cast this
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp hq'

theorem UpperTheory.V.U3.admissible_of_typeII :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W) →
      Af.Adm2 ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    have hconj : ∃ M : GL (Fin 3) (PadicAlgCl l), ∀ g ∈ Ine (F := ℚ) A, D.η g = 1 →
        (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat = (r0 D.η D.ΨQ g).mat * M := by
      have conj_of_close {F Γ : Type} [NormedField F] [IsUltrametricDist F] [Group Γ] [Fintype Γ] {m : ℕ}
          (hΓ : ‖(Fintype.card Γ : F)‖ = 1) (ρ ρ₀ : Γ →* GL (Fin m) F)
          (hi : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1)
          (hc : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ < 1) :
          ∃ M : GL (Fin m) F, ∀ g, (M : Matrix (Fin m) (Fin m) F) * ρ g = ρ₀ g * M := by
        have hi₀ : ∀ g a b, ‖(ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1 := fun g a b => by
          have e : (ρ₀ g : Matrix (Fin m) (Fin m) F) a b = (ρ g : Matrix (Fin m) (Fin m) F) a b +
            -((ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b) := by ring
          rw [e]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hi g a b) (by rw [norm_neg]; exact (hc g a b).le))
        set M : Matrix (Fin m) (Fin m) F := ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g with hM
        have hsplit : M = (Fintype.card Γ : F) • (1 : Matrix (Fin m) (Fin m) F) +
            ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := by
          have e : ∀ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g =
              1 + (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := fun g => by
            rw [Matrix.mul_sub, ← Units.val_mul (ρ₀ g⁻¹) (ρ₀ g), ← map_mul, inv_mul_cancel, map_one, Units.val_one]
            abel
          rw [hM, Finset.sum_congr rfl fun g _ => e g, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Nat.cast_smul_eq_nsmul]
        have hdet : M.det ≠ 0 := by
          rw [hsplit]
          refine UpperTheory.Reformulated.B.Qi6.det_ne_zero _ hΓ _ fun a b => ?_
          rw [Matrix.sum_apply]
          refine UpperTheory.Reformulated.B.Qe17.norm_sum_lt _ _ one_pos fun g _ => ?_
          rw [Matrix.mul_apply]
          refine UpperTheory.Reformulated.B.Qe17.norm_sum_lt _ _ one_pos fun k _ => ?_
          rw [norm_mul, Matrix.sub_apply]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hi₀ _ _ _)).trans_lt (hc g k b)
        refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun h => ?_⟩
        show M * _ = _ * M
        rw [hM, Finset.sum_mul, Finset.mul_sum]
        refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
        simp only [Equiv.coe_mulRight]
        rw [← Matrix.mul_assoc, ← Units.val_mul (ρ₀ h), ← map_mul, map_mul ρ, Units.val_mul, ← Matrix.mul_assoc]
        congr 4
        group
      obtain ⟨-, -, -, -, -, hk0, -, -, -, hK, -⟩ := dat_facts D
      let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ D.η.ker
      let i : H →* D.η.ker := Subgroup.inclusion inf_le_right
      let χ : H →* c.Oˣ := (Chr.dirG ℚ Ω ψ).comp H.subtype
      let ρ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η r h.mult).comp i
      let ρ₀ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η (r0 D.η D.ΨQ) (hasSimilitudeFactor_diagonalRepr _ _)).comp i
      have hkill : ∀ g : H, g ∈ χ.ker → (g : G ℚ Ω) ∈ D.Kill := fun g hg => (hK g).2 ⟨A, hAl, g.2.1, g.2.2, hg⟩
      have hρ : χ.ker ≤ ρ.ker := fun g hg => by
        show (r g).left = 1
        rw [h.kill g (hkill g hg)]; rfl
      have hρ₀ : χ.ker ≤ ρ₀.ker := fun g hg => by
        show tor _ (D.ΨQ g) = 1
        have h1 : tor _ (D.Ψ g) = 1 := congrArg SemidirectProduct.left (hk0 g (hkill g hg))
        have h2 : D.Ψ g = 1 := by
          have : (tor _ (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O) 0 0 = 1 := by rw [h1]; simp
          rw [tor_val] at this
          apply Units.ext
          simpa [wt1] using this
        have h3 : D.ΨQ g = 1 := by
          unfold Dat.ΨQ
          rw [MonoidHom.comp_apply, h2, map_one]
        rw [h3, map_one]
      have hfin : Finite χ.range := by
        have : χ.range ≤ ψ.toUnitHom.range := by
          rintro _ ⟨g, rfl⟩
          exact ⟨_, rfl⟩
        have h2 : Finite ψ.toUnitHom.range := Finite.of_surjective _ ψ.toUnitHom.rangeRestrict_surjective
        exact Finite.of_injective _ (Subgroup.inclusion_injective this)
      have hfinQ : Finite (H ⧸ χ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).symm.toEquiv
      let : Fintype (H ⧸ χ.ker) := Fintype.ofFinite _
      have hpow : ∀ x : H ⧸ χ.ker, x ^ orderOf ψ = 1 := fun x => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
        apply Units.ext
        show ((ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ : c.Oˣ) : c.O) = 1
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
      have hnd : ¬ l ∣ Fintype.card (H ⧸ χ.ker) := fun hd => by
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
        exact D.gd.ord (hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (hpow x)))
      have hnorm : ‖(Fintype.card (H ⧸ χ.ker) : PadicAlgCl l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
        exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd)
      obtain ⟨M, hM⟩ := conj_of_close hnorm (QuotientGroup.lift _ ρ hρ) (QuotientGroup.lift _ ρ₀ hρ₀)
        (fun x a b => by
          obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
          exact h.int g a b)
        (fun x a b => by
          obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
          exact h.red g a b)
      exact ⟨M, fun g hg hη => hM (QuotientGroup.mk (⟨g, hg, hη⟩ : H))⟩
    obtain ⟨M, hMM⟩ := hconj
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    have hconj : ∃ M : GL (Fin 3) (PadicAlgCl l),
        (∀ g ∈ Dec (F := ℚ) A, D.η g = 1 → ∀ a b, wt a b < 0 → (conjBy M r g).mat a b = 0) ∧
          ∀ g ∈ Ine (F := ℚ) A, ∀ a, (conjBy M r g).mat a a = (r0 D.η D.ΨQ g).mat a a := by
      have up_iff {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) :
          (∀ a b, wt a b < 0 → X a b = 0) ↔ X.BlockTriangular id := by
        refine forall_congr' fun a => forall_congr' fun b => imp_congr_left ?_
        show _ ↔ (b : ℕ) < a
        simp only [wt, wt1]
        omega

      have theta_entry {R : Type} [CommRing R] (u : GL (Fin 3) R) (a b : Fin 3) :
          (theta u : Matrix (Fin 3) (Fin 3) R) a b = ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
        rw [theta_val]
        generalize ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v
        fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

      have sgn_up {R : Type} [Field R] (s : ℤˣ) (u : GL (Fin 3) R)
          (hu : ∀ a b, wt a b < 0 → (u : Matrix (Fin 3) (Fin 3) R) a b = 0) :
          (∀ a b, wt a b < 0 → (sgnAct 3 R s u : Matrix (Fin 3) (Fin 3) R) a b = 0) ∧
            ∀ t : Rˣ, (∀ a, (u : Matrix (Fin 3) (Fin 3) R) a a = ((t ^ wt1 a : Rˣ) : R)) →
              ∀ a, (sgnAct 3 R s u : Matrix (Fin 3) (Fin 3) R) a a = ((t ^ wt1 a : Rˣ) : R) := by
        rcases Int.units_eq_one_or s with rfl | rfl
        · rw [sgnAct_one]
          exact ⟨hu, fun _ h => h⟩
        · rw [sgnAct_neg_one]
          have hv : ∀ a b, wt a b < 0 → ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = 0 := by
            rw [up_iff] at hu ⊢
            let := u.invertible
            rw [Matrix.coe_units_inv]
            exact Matrix.blockTriangular_inv_of_blockTriangular hu
          refine ⟨fun a b hab => ?_, fun t ht a => ?_⟩
          · rw [theta_entry]
            refine hv _ _ ?_
            have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
            rwa [this]
          · rw [theta_entry]
            have hd : ∀ i, ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i i *
                (u : Matrix (Fin 3) (Fin 3) R) i i = 1 := by
              intro i
              have e := congrFun (congrFun (Units.inv_mul u) i) i
              have u10 := hu 1 0 (by decide)
              have u20 := hu 2 0 (by decide)
              have u21 := hu 2 1 (by decide)
              have v10 := hv 1 0 (by decide)
              have v20 := hv 2 0 (by decide)
              have v21 := hv 2 1 (by decide)
              generalize ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = v at *
              fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, v10, v20, v21] using e
            have e := hd a.rev
            rw [ht] at e
            have w : wt1 a.rev = -wt1 a := by fin_cases a <;> rfl
            rw [w, _root_.zpow_neg] at e
            exact Units.mul_inv_eq_one.1 e

      have move {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : G) :
          ∃ M : GL (Fin 3) R, ∀ s, (r (g⁻¹ * s * g)).right = 1 →
            (conjBy M r s).left = sgnAct 3 R (r g).right (conjBy h r (g⁻¹ * s * g)).left := by
        let w : GG (m := 3) (R := R) := SemidirectProduct.inr (r g).right
        have hM : GG.ofGL (w * GG.ofGL h * (r g)⁻¹).left = w * GG.ofGL h * (r g)⁻¹ :=
          SemidirectProduct.ext rfl (by simp [w])
        refine ⟨(w * GG.ofGL h * (r g)⁻¹).left, fun s hs => ?_⟩
        have e : conjBy (w * GG.ofGL h * (r g)⁻¹).left r s = w * conjBy h r (g⁻¹ * s * g) * w⁻¹ := by
          show GG.ofGL _ * r s * (GG.ofGL _)⁻¹ = w * (GG.ofGL h * r (g⁻¹ * s * g) * (GG.ofGL h)⁻¹) * w⁻¹
          rw [hM, map_mul, map_mul, map_inv]
          group
        rw [e]
        simp [w]
      obtain ⟨A₀, -, hD, hIn, -, -, -, hc⟩ := dat_loc D
      obtain ⟨x, hxD, hxI⟩ := hc A hAl
      obtain ⟨f, -, hf1, hf2⟩ := h.loc
      obtain ⟨⟨b, hb⟩, -⟩ := @Loc.lemma2b hC.loc l _ c.O _ _ c.dvr _ _ c.fin
        (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (PadicAlgCl l) _ _ _ (r.comp D.ι) ⟨f, hf2, hf1⟩
      obtain ⟨M, hM⟩ := move r b⁻¹ x
      have hη : ∀ s, D.η (x⁻¹ * s * x) = D.η s := fun s => by
        simp only [map_mul, map_inv, inv_mul_cancel_comm]
      have hΨ : ∀ s, D.ΨQ (x⁻¹ * s * x) = D.ΨQ s := fun s => by
        simp only [map_mul, map_inv, inv_mul_cancel_comm]
      have key : ∀ s σ, D.ι σ = x⁻¹ * s * x → D.η s = 1 → (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧
          (σ ∈ Loc.Iq l → ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a) := by
        intro s σ hσ hs
        have h1 : D.η (D.ι σ) = 1 := by rw [hσ, hη, hs]
        have e1 := hM s (by rw [h.mult, hη, hs])
        rw [← hσ] at e1
        obtain ⟨k1, k2⟩ := sgn_up (r x).right (conjBy b⁻¹ r (D.ι σ)).left (hb.tri σ h1)
        rw [← e1] at k1 k2
        refine ⟨k1, fun hσI a => ?_⟩
        rw [show (r0 D.η D.ΨQ s).mat a a = ((D.ΨQ s ^ wt1 a : (PadicAlgCl l)ˣ) : PadicAlgCl l) by
          simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq]]
        refine k2 (D.ΨQ s) (fun a => (hb.ine σ hσI h1 a).trans ?_) a
        rw [← hΨ, ← hσ]
        exact congrArg Units.val (map_zpow (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) (D.Ψ (D.ι σ)) (wt1 a))
      have kI : ∀ s ∈ Ine (F := ℚ) A, D.η s = 1 ∧ (∀ a a', wt a a' < 0 → (conjBy M r s).mat a a' = 0) ∧
          ∀ a, (conjBy M r s).mat a a = (r0 D.η D.ΨQ s).mat a a := by
        intro s hs
        have := (hxI s).1 hs
        rw [← hIn] at this
        obtain ⟨σ, hσI, hσ⟩ := this
        have h1 : D.η s = 1 := by rw [← hη, ← hσ]; exact D.η_unr σ hσI
        exact ⟨h1, (key s σ hσ h1).1, (key s σ hσ h1).2 hσI⟩
      refine ⟨M, fun s hs h1 => ?_, fun s hs => (kI s hs).2.2⟩
      have := (hxD s).1 hs
      rw [← hD] at this
      obtain ⟨σ, hσ⟩ := this
      exact (key s σ hσ h1).1
    obtain ⟨M, hup, hdiag⟩ := hconj
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      refine eigvec M _ _ ?_ fun i j hij => ?_
      · rw [← conj_mat M r s hr, hdiag s hs 0]
        simp [GG.mat, tor_val, wt1]
      · rw [← conj_mat M r s hr]
        exact hup s (hID hs) (hIk hs) i j hij
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · obtain ⟨s, hs, hn⟩ := exists_two D.gd.l_odd A hAl
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
