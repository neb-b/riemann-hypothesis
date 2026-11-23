module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.IneInf
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ine_of_emb {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [Algebra ℚ Ω]
    [IsScalarTower ℚ L Ω] (A : ValuationSubring Ω) (s : G L Ω)
    (h : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A) : s ∈ Ine (F := L) A := h

theorem UpperTheory.V.Z.Sym.Ga.ineInf :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∈ Ine (F := L) A ∧ ¬ IsOfFinOrder (cycBar L Ω l s) := by
  intro L Ω _ _ _ _ _ l _ A hA H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L Ω⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  haveI : Finite (G L Ω ⧸ H) := H.quotient_finite_of_isOpen hH
  obtain ⟨hemb, -, hidx⟩ := Base.galEmbTop ℚ L Ω
  have hrange : (Base.galEmb ℚ L Ω).range = Base.galOf ℚ L Ω := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact Base.galEmb_mem ℚ L Ω s
    · intro σ hσ
      refine ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x }, ?_⟩
      ext x
      rw [Base.galEmb_apply]
      rfl
  have hfin : (H.map (Base.galEmb ℚ L Ω)).index ≠ 0 := by
    rw [H.index_map_of_injective hemb.injective, hrange, hidx]
    exact mul_ne_zero Subgroup.index_ne_zero_of_finite Module.finrank_pos.ne'
  haveI : (H.map (Base.galEmb ℚ L Ω)).FiniteIndex := ⟨hfin⟩
  have hu : IsUnit ((1 : ℤ_[l]) + l) := by
    by_contra h
    have h1 : (l : ℤ_[l]) ∣ 1 + l :=
      (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr h))
    have hl : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_one ((dvd_add_left (dvd_refl _)).mp h1)
    have h2 : ‖(l : ℤ_[l])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr (dvd_refl _)
    rw [PadicInt.isUnit_iff.mp hl] at h2
    exact lt_irrefl _ h2
  have hv : ¬ IsOfFinOrder hu.unit := by
    intro hv
    obtain ⟨n, hn, hpow⟩ := hv.exists_pow_eq_one
    have h2 : ((1 : ℤ_[l]) + l) ^ n = 1 := by
      have := congrArg Units.val hpow
      simpa using this
    have h3 : ((1 + l) ^ n : ℕ) = 1 := by
      exact_mod_cast h2
    rcases Nat.pow_eq_one.mp h3 with h4 | h4
    · have := (Fact.out : l.Prime).pos
      omega
    · omega
  obtain ⟨τ, hτ, hτv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  have hpow : τ ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index ∈ H.map (Base.galEmb ℚ L Ω) :=
    Subgroup.normalCore_le _ (Subgroup.pow_index_mem _ τ)
  obtain ⟨s, hs, hsτ⟩ := hpow
  have hsI : Base.galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := by
    rw [hsτ]
    exact Subgroup.pow_mem _ hτ _
  refine ⟨s, hs, ine_of_emb A s hsI, ?_⟩
  have hcyc : cycZ L Ω l s = cycZ ℚ Ω l (Base.galEmb ℚ L Ω s) := by
    simp only [cycZ, MonoidHom.comp_apply]
    congr 1
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hmap : Function.Injective (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l)) := by
    intro a b hab
    exact Units.ext (hinj (congrArg Units.val hab))
  intro hfo
  have hval : cycBar L Ω l s = Units.map ((algebraMap ℚ_[l] (Qbar l)).comp
      PadicInt.Coe.ringHom : ℤ_[l] →* Qbar l) (hu.unit ^ (H.map (Base.galEmb ℚ L Ω)).normalCore.index) := by
    simp only [cycBar, MonoidHom.comp_apply, hcyc, hsτ, map_pow, hτv]
    rfl
  rw [hval, ← orderOf_pos_iff, orderOf_injective _ hmap, orderOf_pos_iff, isOfFinOrder_pow] at hfo
  rcases hfo with h | h
  · exact hv h
  · exact Subgroup.FiniteIndex.index_ne_zero h
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TrPair
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.trPair :
    ∀ (k : Type) [Field k] (n : ℕ) (g g' P : GL (Fin n) k) (μ : kˣ), (g : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (g' : Matrix (Fin n) (Fin n) k) = (μ : k) • (P : Matrix (Fin n) (Fin n) k) → Ga.tr g' = μ * Ga.tr g⁻¹ := by
  intro k _ n g g' P μ h
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k)
  set Ai : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set B : Matrix (Fin n) (Fin n) k := (g' : Matrix (Fin n) (Fin n) k)
  set M : Matrix (Fin n) (Fin n) k := (P : Matrix (Fin n) (Fin n) k)
  set Mi : Matrix (Fin n) (Fin n) k := ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hA : A * Ai = 1 := g.mul_inv
  have hM : Mi * M = 1 := P.inv_mul
  have hM' : M * Mi = 1 := P.mul_inv
  have hB : B = Mi * Aiᵀ * (Aᵀ * M * B) := by
    have : Aiᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA, Matrix.transpose_one]
    calc B = Mi * M * B := by rw [hM, Matrix.one_mul]
      _ = Mi * (Aiᵀ * Aᵀ) * M * B := by rw [this, Matrix.mul_one]
      _ = Mi * Aiᵀ * (Aᵀ * M * B) := by simp only [Matrix.mul_assoc]
  show B.trace = μ * Ai.trace
  rw [hB, h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hM', Matrix.one_mul, Matrix.trace_transpose]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TraceSym4M
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_sym4M {k : Type} [Field k] (g : Matrix (Fin 2) (Fin 2) k) :
    Matrix.trace (UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix k g) = g.trace ^ 4 - 3 * g.trace ^ 2 * g.det + g.det ^ 2 := by
  simp only [UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.trace, Matrix.diag,
    Fin.sum_univ_five, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

theorem UpperTheory.V.Z.Sym.Ga.trSym4 :
    ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (Ga.sym4 ρ s) = Ga.uf (ρ s) ^ 2 + Ga.uf (ρ s) - 1 := by
  intro k _ Γ _ ρ s
  have hD : ((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
    ((ρ s).isUnit.map Matrix.detMonoidHom).ne_zero
  simp only [Ga.tr, Ga.uf, Ga.sym4, UpperTheory.V.Af.tw_val, Matrix.trace_smul, Units.coe_map,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe, trace_sym4M]
  simp only [MonoidHom.pow_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    smul_eq_mul]
  field_simp
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Sym.Ga.det_ne {k : Type} [Field k] (g : GL (Fin 2) k) :
    (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
  (Matrix.isUnits_det_units g).ne_zero

private theorem UpperTheory.V.Z.Sym.Ga.det_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = ((g : Matrix (Fin 2) (Fin 2) k).det)⁻¹ := by
  have h : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

private theorem UpperTheory.V.Z.Sym.Ga.trace_inv {k : Type} [Field k] (g : GL (Fin 2) k) :
    ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace =
      (g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.trace_smul,
    Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  rw [div_eq_inv_mul, add_comm]

theorem UpperTheory.V.Z.Sym.Ga.ufFacts :
    ∀ (k : Type) [Field k] (g : GL (Fin 2) k), (∀ a b : kˣ, (g : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (a : k)) * (X - C (b : k)) → Ga.uf g = (a / b : kˣ) + ((a / b : kˣ)⁻¹ : kˣ)) ∧ Ga.uf g⁻¹ = Ga.uf g ∧ (∀ x : GL (Fin 2) k, Ga.uf (x * g * x⁻¹) = Ga.uf g) ∧ (∀ (g' P : GL (Fin 2) k) (μ : kˣ), (g : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) * (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (P : Matrix (Fin 2) (Fin 2) k) → Ga.uf g' = Ga.uf g) ∧ ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (ad0 ρ s) = Ga.uf (ρ s) + 1 := by
  intro k _ g
  have hd := Ga.det_ne g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h' := h
    rw [Matrix.charpoly_fin_two] at h'
    have e0 := congrArg (Polynomial.eval 0) h'
    have e1 := congrArg (Polynomial.eval 1) h'
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
    have hdet : (g : Matrix (Fin 2) (Fin 2) k).det = a * b := by linear_combination e0
    have htr : (g : Matrix (Fin 2) (Fin 2) k).trace = a + b := by linear_combination e0 - e1
    have ha : (a : k) ≠ 0 := a.ne_zero
    have hb : (b : k) ≠ 0 := b.ne_zero
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdet, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    field_simp
    ring
  · simp only [Ga.uf, Ga.tr]
    rw [Ga.trace_inv, Ga.det_inv]
    field_simp
  · intro x
    have hx : ((x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (x : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have ht : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (g : Matrix (Fin 2) (Fin 2) k).trace := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hx, Matrix.one_mul]
    have hdt : ((x * g * x⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (g : Matrix (Fin 2) (Fin 2) k).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, mul_comm, Matrix.det_mul, ← mul_assoc, ← Matrix.det_mul, hx,
        Matrix.det_one, one_mul]
    simp only [Ga.uf, Ga.tr]
    rw [ht, hdt]
  · intro g' P μ h
    have hμ : (μ : k) ≠ 0 := μ.ne_zero
    have hP := Ga.det_ne P
    have hPi : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPi' : ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (P : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hg : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (g : Matrix (Fin 2) (Fin 2) k)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    have hform : (g' : Matrix (Fin 2) (Fin 2) k) = (μ : k) • (((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k)) := by
      have e := congrArg (fun M => ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ * M) h
      rw [Matrix.mul_smul] at e
      rw [← e]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)ᵀ) ((g : Matrix (Fin 2) (Fin 2) k)ᵀ), hg,
        Matrix.one_mul, ← Matrix.mul_assoc, hPi', Matrix.one_mul]
    have htr : (g' : Matrix (Fin 2) (Fin 2) k).trace =
        μ * ((g : Matrix (Fin 2) (Fin 2) k).trace / (g : Matrix (Fin 2) (Fin 2) k).det) := by
      rw [hform, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul,
        Matrix.trace_transpose, Ga.trace_inv, smul_eq_mul]
    have hdt : (g' : Matrix (Fin 2) (Fin 2) k).det = μ ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det := by
      have e := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at e
      field_simp
      have : (P : Matrix (Fin 2) (Fin 2) k).det * ((g' : Matrix (Fin 2) (Fin 2) k).det * (g : Matrix (Fin 2) (Fin 2) k).det) =
          (P : Matrix (Fin 2) (Fin 2) k).det * (μ : k) ^ 2 := by linear_combination e
      exact mul_left_cancel₀ hP this
    simp only [Ga.uf, Ga.tr]
    rw [htr, hdt]
    field_simp
  · intro Γ _ ρ s
    have hd' := Ga.det_ne (ρ s)
    have e : (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) =
        (((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹) • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
      rw [ad0, tw_val]
      simp [Matrix.GeneralLinearGroup.det]
    simp only [Ga.tr, Ga.uf]
    rw [e, Matrix.trace_smul, Matrix.trace_fin_two, Matrix.trace_fin_three]
    have hd2 := hd'
    rw [Matrix.det_fin_two] at hd2 ⊢
    simp [symSquareMatrixHom]
    field_simp
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.WtOf
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem infOfWeight_reflect_eq_weights (lam : DomWeight 2) : (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) = ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) := by
  simp only [infOfWeight, Multiset.map_map, Function.comp_def, Fin.univ_val_map]
  simp [List.ofFn_succ]
  rw [← Multiset.cons_coe, Multiset.coe_singleton]
  congr 2
  ring

theorem UpperTheory.V.Z.Sym.Ga.wtOf :
    ∀ (m : ℕ) (b : ℤ) (lam : DomWeight 2), ({b, b + m} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) → lam.w 0 - lam.w 1 = (m : ℤ) - 1 := by
  intro m b lam h
  rw [infOfWeight_reflect_eq_weights] at h
  have hz : ({b, b + m} : Multiset ℤ) = {-lam.w 0, 1 - lam.w 1} :=
    Multiset.map_injective Int.cast_injective h
  have hanti : lam.w 1 ≤ lam.w 0 := lam.anti (by decide)
  have hs := congrArg Multiset.sum hz
  simp at hs
  have hb : b ∈ ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ) := by
    rw [← hz]; simp
  simp at hb
  rcases hb with hb | hb <;> omega
end
end

