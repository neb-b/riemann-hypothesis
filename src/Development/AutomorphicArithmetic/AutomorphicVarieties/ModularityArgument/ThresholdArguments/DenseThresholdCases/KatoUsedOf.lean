module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
open scoped Matrix
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
theorem UpperTheory.V.Z.Kato.used_of_alt :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))}
      {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} (_ : D.IsPt U g₁ r),
      TypeII D.η r → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → Continuous W →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = Wfun r g) →
      (∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).det = ((D.η g : ℤˣ) : ℤ)) →
      ∀ ι : Qbar l ≃+* ℂ, D.IsModularDense ι W →
      UpperTheory.V.Z.Kato.Used l Ω K e N ((Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η)
        ((Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)) W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h hII W hext hcont hW hdet ι hmod
  obtain ⟨h11, -, -⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, hηc, hΨc, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨A₀, hA₀, -, hIn, -, -, hcyc, hconj⟩ := dat_loc D
  set θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η with hθdef
  set ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ) with hψdef
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hord := typeII_ord hC D hM h hII W hext hcont hdet
  have w0 : wt1 0 = 1 := by decide
  have w1 : wt1 1 = 0 := by decide
  have w2 : wt1 2 = -1 := by decide
  have h00 : ∀ g, (r0 D.η D.ΨQ g).mat 0 0 = (D.ΨQ g : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w0, _root_.zpow_one]
  have h22 : ∀ g, (r0 D.η D.ΨQ g).mat 2 2 = (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w2, _root_.zpow_neg, _root_.zpow_one]
  have h11' : ∀ g, (r0 D.η D.ΨQ g).mat 1 1 = 1 := fun g => by
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq, w1, _root_.zpow_zero, Units.val_one]
  have htrW : ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)).trace = (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 := by
    intro g
    rw [hW, Wfun, hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · rw [hg, if_pos rfl, Matrix.trace_fin_two]
      show (r g).mat 0 0 + (r g).mat 2 2 = _
      simp
    · rw [hg, if_neg (by decide), Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.mul_diagonal]
      show (r g).mat 0 0 * (-1) + (r g).mat 2 2 * 1 = _
      simp
  refine
    { l_odd := D.gd.l_odd, e_pos := D.gd.e_pos, gen := D.gd.gen, quad := D.gd.quad, imag := D.gd.imag, l_cop := D.gd.l_cop,
      N_pos := NeZero.pos N, N_even := D.gd.N_even, cop := D.gd.cop, θ_ker := ?_, θ_sq := fun g => ?_, ψ_mu := fun s hs => ?_,
      ψ_ord := ⟨orderOf ψ, D.gd.ord, fun g => ?_⟩, ψ_ine := fun A hA s hs => ?_, even := ⟨D.cc, D.conj, ?_⟩,
      level := hord.1, ord := ⟨A₀, N, hA₀, NeZero.pos N, hord.2 A₀ hA₀⟩, det := fun g => by rw [hdet, hθ0],
      tr_ine := fun A hA s hs => ?_, red := fun g => ?_, flag := ?_, irr := typeII_irr_cyc hC D hM h hII W hext }
  · rw [← D.η_ker]
    ext g
    simp only [MonoidHom.mem_ker, Units.ext_iff, hθ0, Units.val_one]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> rw [hg] <;> norm_num
  · show Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom (D.η g) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N s)) = 1
    rw [cls_eq_one N s hs, map_one, map_one]
  · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow]
    have : ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe,
        Units.val_one]
    rw [this, map_one]
  · obtain ⟨x, -, hxI⟩ := hconj A hA
    have h1 := (hxI s).1 hs
    rw [← hIn] at h1
    obtain ⟨σ, hσI, hσ⟩ := h1
    have h2 := D.Ψ_I σ hσI
    have h3 : Loc.cycA l l c.O σ = chiO ℚ Ω l c.O (D.ι σ) := by
      show Units.map _ (Loc.cyc l l σ) = Units.map _ (cycZ ℚ Ω l (D.ι σ))
      rw [hcyc]
      rfl
    have h4 : Chr.dirG ℚ Ω ψ (D.ι σ) = Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) := by
      rw [h3, Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, _root_.zpow_natCast] at h2
      exact mul_left_cancel h2
    have h5 : Chr.dirG ℚ Ω ψ s = Chr.dirG ℚ Ω ψ (D.ι σ) := by
      rw [hσ]
      simp only [map_mul, map_inv, inv_mul_cancel_comm]
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Chr.dirG ℚ Ω ψ s) ^ 2 = 1
    have h6 : Chr.dirG ℚ Ω (comp l ψ) (D.ι σ) ^ 2 = 1 := by
      apply Units.ext
      show (((comp l ψ).toUnitHom (Chr.cls ℚ Ω N (D.ι σ)) ^ 2 : c.Oˣ) : c.O) = _
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, D.gd.ine, MulChar.one_apply_coe,
        Units.val_one]
    rw [← map_pow, h5, h4, h6, map_one]
  · rw [← hΨ]
    show Units.map _ (D.Ψ D.cc) = 1
    rw [hΨc, map_one]
  · obtain ⟨hch, -⟩ := pt_inertia_above hC D hM h A hA
    have hk : s ∈ D.η.ker := (hl1 A hA).1 hs
    have htr : (r s).mat.trace = (r0 D.η D.ΨQ s).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hch s hs]
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three, h00, h22, h11', h11 s hk] at htr
    rw [htrW, ← hΨ, hθ0, show D.η s = 1 from hk]
    simp only [Units.val_one, Int.cast_one, one_mul]
    linear_combination htr
  · rw [htrW, ← hΨ]
    have a0 := h.red g 0 0
    have a2 := h.red g 2 2
    rw [h00] at a0
    rw [h22] at a2
    have hn : ‖(θ g : PadicAlgCl l)‖ = 1 := by
      rw [hθ0]
      rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
    have e1 : (θ g : PadicAlgCl l) * (r g).mat 0 0 + (r g).mat 2 2 -
        ((θ g : PadicAlgCl l) * (D.ΨQ g : PadicAlgCl l) + (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) =
        (θ g : PadicAlgCl l) * ((r g).mat 0 0 - D.ΨQ g) + ((r g).mat 2 2 - (((D.ΨQ g)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l)) := by
      ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ a2)
    rw [norm_mul, hn, one_mul]
    exact a0
  · let χ : G ℚ Ω →* (Qbar l)ˣ :=
      (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
    have hχ2 (g : G ℚ Ω) : χ g * χ g = 1 := by
      have hχg : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
        apply Units.ext
        show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
        rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
      show Units.map _ _ * Units.map _ _ = 1
      rw [← map_mul, hχg, map_one]
    have hψχ : ∀ s ∈ Ine (F := ℚ) A₀, ψQ s = χ s := fun s hs => by
      rw [← hIn] at hs
      obtain ⟨g, hg, rfl⟩ := hs
      show Units.map _ _ = Units.map _ _
      rw [GlobalTheory.Ord2.psi_ine D g hg]
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A₀ hA₀
    have hlocal : ∃ κ : Fin 2 → ↥(Dec (F := ℚ) A₀) →* (Qbar l)ˣ,
        Af.IsFlagOn W (Dec (F := ℚ) A₀) κ ∧
          ∀ s : ↥(Dec (F := ℚ) A₀), (s : G ℚ Ω) ∈ Ine (F := ℚ) A₀ →
            κ 0 s = D.ΨQ s ∧ κ 1 s = (D.ΨQ s)⁻¹ := by
      have hblk (s : G ℚ Ω) (hs : s ∈ D.η.ker) :
          (r s).mat = !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] := by
        have hcorner : (W s : Matrix (Fin 2) (Fin 2) (Qbar l)) = corner (r s).mat := hext.1 s hs
        have e01 := hII.1 s hs 0 1 (by decide)
        have e10 := hII.1 s hs 1 0 (by decide)
        have e12 := hII.1 s hs 1 2 (by decide)
        have e21 := hII.1 s hs 2 1 (by decide)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hcorner, corner, e01, e10, e12, e21, h11 s hs]
      obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A₀ hA₀
      obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A₀ hl.out hA₀
      have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
        have hu' := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
        rwa [map_sub, map_pow, map_one, sub_ne_zero] at hu'
      set v : Fin 3 → Qbar l :=
        ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ Pi.single 0 1 with hv
      have hv0 : v ≠ 0 := fun h0 => by
        have he := congrArg (fun x => ((M : Matrix (Fin 3) (Fin 3) (Qbar l)) *ᵥ x) 0) (hv.symm.trans h0)
        simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at he
        simp at he
      have hev : ∀ s ∈ Ine (F := ℚ) A₀,
          !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := by
        intro s hs
        have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
        have hmat : (conjBy M r s).mat =
            (M : Matrix (Fin 3) (Fin 3) (Qbar l)) * (r s).mat *
              ((M⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) := by
          simp [conjBy, GG.mat, hr]
        have hcol : (conjBy M r s).mat *ᵥ Pi.single 0 1 =
            (D.ΨQ s : Qbar l) • (Pi.single 0 1 : Fin 3 → Qbar l) := by
          rw [Matrix.mulVec_single_one]
          funext i
          fin_cases i
          · change (conjBy M r s).mat 0 0 = _
            rw [hdiag s hs 0, h00]
            simp
          · simpa using hup s (hID hs) (hIk hs) 1 0 (by decide)
          · simpa using hup s (hID hs) (hIk hs) 2 0 (by decide)
        rw [← hblk s (hIk hs), hv, ← Matrix.mulVec_smul, ← hcol, hmat,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      have hv1 : v 1 = 0 := by
        have he := congrFun (hev s₀ hs₀) 1
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at he
        by_contra hne
        have hval : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans he)).symm
        exact hs₀' (by rw [hval, one_pow])
      exact UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A₀) (Ine (F := ℚ) A₀) W D.ΨQ ![v 0, v 2]
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
    obtain ⟨κ, hflag, hκ⟩ := hlocal
    refine ⟨A₀, χ, κ, ?_, ?_, hflag, ?_, ?_⟩
    · obtain ⟨hex, htop, hover, -⟩ := places ℚ Ω l A₀
      have hne : A₀ ≠ ⊤ := fun ht => (htop ht).2 hA₀
      obtain ⟨v, hv⟩ := hex hne
      exact ⟨v, hv, (hover v hv).1 hA₀⟩
    · intro s hs
      show Units.map _ _ = 1
      rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
    · intro s hs
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [hθ0, hIk hs]
      simp
    · intro s hs
      rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← _root_.zpow_neg]
      refine ⟨rfl, ?_⟩
      congr 1
      exact inv_eq_of_mul_eq_one_right (hχ2 s)
end
