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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ClsEqOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cls_eq_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ) : Chr.cls ℚ Ω N g = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec N g ζ hζ.pow_eq_one
  rw [hg ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ (1 : ZMod N).val = ζ := by
    rw [ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  apply Units.ext
  apply ZMod.val_injective
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2.symm)

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

private theorem conj_mat {Γ k : Type} [Group Γ] [Field k] (M : GL (Fin 3) k)
    (r : Γ →* GG (m := 3) (R := k)) (g : Γ)
    (hg : (r g).right = 1) : (conjBy M r g).mat = (M : Matrix (Fin 3) (Fin 3) k) * (r g).mat * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  simp [conjBy, GG.mat, hg]

private theorem eigvec {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
    (h0 : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
    (h : ∀ i j, wt i j < 0 → ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
    X *ᵥ (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) =
      a • (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
  have e : ((M : Matrix (Fin 3) (Fin 3) k) * X * ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *ᵥ Pi.single 0 1 =
      a • Pi.single 0 1 := by
    rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h 1 0 (by decide)
    · simpa using h 2 0 (by decide)
  rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

private theorem exists_two {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
  have hu : IsUnit ((2 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 h2
  obtain ⟨u, hu⟩ := hu
  obtain ⟨s, hs, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  refine ⟨s, hs, fun n hn => ?_⟩
  have e2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = ((2 : ℚ) : Qbar l) := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) (cycZ ℚ Ω l s : ℤ_[l]) = _
    rw [e, hu, map_natCast]
    simp
  have e3 := congrArg Units.val hn
  rw [Units.val_zpow_eq_zpow_val, e2, Units.val_one, ← Rat.cast_zpow] at e3
  have e4 : (2 : ℚ) ^ n = 1 := by exact_mod_cast e3
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 e4

theorem UpperTheory.V.U3.typeII_ord :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (_ : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → Continuous W →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ)) →
      Af.Level l (N * (discr K).natAbs) ![(e : ℤ), -(e : ℤ)] W ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A, (∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) →
        (W s : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).charpoly =
          (Polynomial.X - Polynomial.C ((cycBar ℚ Ω l s ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l)) *
            (Polynomial.X - Polynomial.C ((cycBar ℚ Ω l s ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l)) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hcont hdet
  obtain ⟨h11, -, -⟩ := typeII_facts hC D hM h hII
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
  refine ⟨⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, fun A hAl s hs hfix => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
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
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
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
  · obtain ⟨hch, -⟩ := pt_inertia_above hC D hM h A hAl
    have hk : s ∈ D.η.ker := (hl1 A hAl).1 hs
    have hψ : ψQ s = 1 := by
      show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N s)) = 1
      rw [cls_eq_one N s hfix, map_one, map_one]
    have htr : (r s).mat.trace = (r0 D.η D.ΨQ s).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hch s hs]
    have hd : (W s : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = 1 := by
      rw [hdet, show D.η s = 1 from hk]; simp
    have hu : ((cycBar ℚ Ω l s ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) * ((cycBar ℚ Ω l s ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero, Units.val_one]
    have ht : (W s : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).trace =
        ((cycBar ℚ Ω l s ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) + ((cycBar ℚ Ω l s ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) := by
      rw [hblk s hk, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hψ, mul_one, Matrix.trace_diagonal, Matrix.trace_fin_three,
        Fin.sum_univ_three] at htr
      rw [Matrix.trace_fin_two, _root_.zpow_neg]
      have w0 : wt1 0 = 1 := by decide
      have w1 : wt1 1 = 0 := by decide
      have w2 : wt1 2 = -1 := by decide
      simp only [w0, w1, w2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        Matrix.cons_val_fin_one, _root_.zpow_one, _root_.zpow_zero, _root_.zpow_neg, Units.val_one] at htr
      linear_combination htr
    rw [Matrix.charpoly_fin_two, ht, hd, ← hu, map_add (f := _), map_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem matIrr_ker {Γ κ Z : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] [CommGroup Z]
    (ρ : Γ →* GL (Fin 2) κ) (χ : Γ →* Z) (I : Subgroup Γ) (Ψ : Γ →* κˣ)
    (hsurj : ∀ g, ∃ s ∈ I, χ s = χ g)
    (htr : ∀ s ∈ I, (ρ s : Matrix (Fin 2) (Fin 2) κ).trace = (Ψ s : κ) + (Ψ s : κ)⁻¹)
    (hinf : ∃ u ∈ I, Ψ u ^ 8 ≠ 1)
    (hirr : MatIrr ⊤ fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ)) :
    MatIrr χ.ker fun g => (ρ g : Matrix (Fin 2) (Fin 2) κ) := by
  by_contra hred
  obtain ⟨φ, h1, hker, h2, M, hM⟩ := exists_selfTwist ρ χ.ker (fun a b => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (χ a) (χ b), mul_inv_cancel_right, mul_inv_cancel]) hirr hred
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 1 := by
    by_contra hne
    push Not at hne
    exact h1 (MonoidHom.ext hne)
  obtain ⟨s, hs, hsg⟩ := hsurj g
  have hφs : φ s ≠ 1 := by
    intro h
    have : φ (s⁻¹ * g) = 1 := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, inv_mul_cancel])
    rw [map_mul, map_inv, h, inv_one, one_mul] at this
    exact hg this
  have key : ∀ t ∈ I, φ t ≠ 1 → Ψ t ^ 4 = 1 := by
    intro t ht hφ
    have e : (φ t : κ) • (ρ t : Matrix (Fin 2) (Fin 2) κ) =
        ((M⁻¹ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) * (ρ t * M) := by
      rw [← hM t trivial, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have e2 := congrArg Matrix.trace e
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      htr t ht, smul_eq_mul] at e2
    have e3 : (φ t : κ) - 1 ≠ 0 := fun h => hφ (Units.ext (sub_eq_zero.1 h))
    have e4 : (Ψ t : κ) + (Ψ t : κ)⁻¹ = 0 := by
      refine (mul_eq_zero.1 (?_ : ((φ t : κ) - 1) * _ = 0)).resolve_left e3
      rw [sub_mul, e2, one_mul, sub_self]
    have e5 : (Ψ t : κ) * (Ψ t : κ)⁻¹ = 1 := mul_inv_cancel₀ (Ψ t).ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination ((Ψ t : κ) ^ 3 - (Ψ t : κ)) * e4 - ((Ψ t : κ) ^ 2 - 1) * e5
  obtain ⟨u, hu, hu8⟩ := hinf
  have hu2 : φ (u ^ 2) = 1 := by
    rw [map_pow]
    exact DFunLike.congr_fun h2 u
  have h3 := key (s * u ^ 2) (mul_mem hs (pow_mem hu 2)) (by rwa [map_mul, hu2, mul_one])
  rw [map_mul, mul_pow, key s hs hφs, one_mul, map_pow, ← pow_mul] at h3
  exact hu8 h3

private theorem exists_unit_pow_ne (l : ℕ) [Fact l.Prime] : ∃ v : ℤ_[l]ˣ, ∀ n : ℕ, n ≠ 0 → v ^ n ≠ 1 := by
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  refine ⟨hu.unit, fun n hn h => ?_⟩
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
  have h3 : (1 + l) ^ n = 1 := by exact_mod_cast h2
  have := (Fact.out : l.Prime).pos
  rcases Nat.pow_eq_one.1 h3 with h4 | h4
  · omega
  · exact hn h4

theorem UpperTheory.V.U3.typeII_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W →
        Af.IsIrr ((W.comp (galEmb ℚ K Ω)).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h hII W hW
  obtain ⟨A, hA, -, hIn, -⟩ := dat_loc D
  have hIK : Ine (F := ℚ) A ≤ D.η.ker := ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hch : ∀ g ∈ Ine (F := ℚ) A, (r g).mat.charpoly = (r0 D.η D.ΨQ g).mat.charpoly := by
    intro g hg
    rw [← hIn] at hg
    obtain ⟨σ, hσ, rfl⟩ := hg
    obtain ⟨f, -, hf1, hf2⟩ := h.loc
    have hlocal := (@Loc.lemma2a hC.loc l _ c.O _ _ c.dvr _ _ c.fin
      (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1 D.loc U (PadicAlgCl l) _ _
      (r.comp D.ι) ⟨f, hf2, hf1⟩).1 σ hσ
    change (r (D.ι σ)).mat.charpoly = _ at hlocal
    rw [hlocal]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val]
    rw [Matrix.charpoly_of_isUpperTriangular _ (Matrix.blockTriangular_diagonal _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.diagonal_apply_eq]
    congr 2
    exact congrArg Units.val
      (map_zpow (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) (D.Ψ (D.ι σ)) (wt1 i))
  have h11 := (typeII_facts hC D hM h hII).1
  have hmem : ∀ s, galEmb ℚ K Ω s ∈ D.η.ker := fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hlift : ∀ g ∈ D.η.ker, ∃ s, galEmb ℚ K Ω s = g := fun g hg => by
    rw [D.η_ker, ← range_galEmb] at hg
    exact hg
  have hsur : ∀ v : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = v := fun v => by
    obtain ⟨σ, hσ, hv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
    obtain ⟨s, rfl⟩ := hlift σ (hIK hσ)
    exact ⟨s, hσ, hv⟩
  have main := matIrr_ker (W.comp (galEmb ℚ K Ω)) (cycBar K Ω l) ((Ine (F := ℚ) A).comap (galEmb ℚ K Ω))
    (D.ΨQ.comp (galEmb ℚ K Ω)) (fun g => ?_) (fun s hs => ?_) ?_ (fun X hX => ?_)
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun X _ hX => main X fun g hg v hv => hX ⟨g, hg⟩ v hv⟩
  · obtain ⟨s, hs, hv⟩ := hsur (cycZ K Ω l g)
    refine ⟨s, hs, ?_⟩
    simp only [cycBar, MonoidHom.comp_apply, hv]
  · have h1 := Matrix.trace_eq_neg_charpoly_coeff (r (galEmb ℚ K Ω s)).mat
    rw [hch _ hs, ← Matrix.trace_eq_neg_charpoly_coeff] at h1
    rw [MonoidHom.comp_apply, hW.1 _ (hmem s), MonoidHom.comp_apply]
    have h2 := h11 _ (hmem s)
    have h3 : (corner (r (galEmb ℚ K Ω s)).mat).trace =
        (r (galEmb ℚ K Ω s)).mat 0 0 + (r (galEmb ℚ K Ω s)).mat 2 2 := Matrix.trace_fin_two _
    have h4 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l) + 1 +
        (D.ΨQ (galEmb ℚ K Ω s) : PadicAlgCl l)⁻¹ := by
      simp [GG.mat, tor_val, wt1, Fin.sum_univ_three]
    rw [Matrix.trace_fin_three, h4, h2] at h1
    rw [h3]
    linear_combination h1
  · obtain ⟨v, hv⟩ := exists_unit_pow_ne l
    obtain ⟨s, hs, hsv⟩ := hsur v
    refine ⟨s, hs, fun h8 => ?_⟩
    have ho : orderOf ψ ≠ 0 := fun h0 => D.gd.ord (h0 ▸ dvd_zero l)
    have he : e ≠ 0 := Nat.one_le_iff_ne_zero.1 D.gd.e_pos
    have h1 : D.Ψ (galEmb ℚ K Ω s) ^ 8 = 1 := by
      apply Units.ext
      apply Subtype.val_injective
      have := congrArg Units.val h8
      exact this
    have h2 : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
        ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    have h3 : D.Ψ (galEmb ℚ K Ω s) = Units.map (algebraMap ℤ_[l] c.O).toMonoidHom v ^ e *
        Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) := by
      rw [← hsv, ← zpow_natCast]
      rfl
    have h4 : Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (v ^ (e * (8 * orderOf ψ))) = 1 := by
      have := congrArg (· ^ orderOf ψ) h1
      simp only [one_pow] at this
      rw [← pow_mul, h3, mul_pow, mul_comm 8, pow_mul (Chr.dirG ℚ Ω ψ _), h2, one_pow, mul_one,
        ← pow_mul, mul_comm _ 8] at this
      rw [map_pow, this]
    refine hv (e * (8 * orderOf ψ)) (mul_ne_zero he (mul_ne_zero (by norm_num) ho)) ?_
    have hinj : Function.Injective (algebraMap ℤ_[l] c.O) := fun x y hxy => by
      have : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) y] at this
      exact Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective this)
    exact (Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hinj) (h4.trans (map_one _).symm)
  · refine hII.2 X fun g hg v hv => ?_
    obtain ⟨s, rfl⟩ := hlift g hg
    have := hX s trivial v hv
    simp only [MonoidHom.comp_apply, hW.1 _ hg] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LiftingTheory
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG (m := m) (R := R))
    (h1 : x.mat = 1) (h2 : x.right = -1) (h3 : y.right = 1) :
    (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]
end

