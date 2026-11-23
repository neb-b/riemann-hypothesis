module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RingEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) := by
  intro a b h
  ext x
  apply hf
  have hx := congrArg (fun χ : DirichletCharacter O' N => χ (x : ZMod N)) h
  simpa [chHom, MulChar.ringHomComp_apply] using hx

private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  ext x
  simp [chHom, HV.comp, MulChar.ringHomComp_apply]

private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  have ho : orderOf (chHom f χ) = orderOf χ := orderOf_injective (chHom f) (chHom_inj f hf) χ
  have hl : chHom f (lPart l χ) = lPart l (chHom f χ) := by
    simp only [lPart, map_pow, ho]
  simp only [chiP, th0, lPrime, map_mul, map_inv, hl, chHom_comp]

private theorem gd_chHom (hf : Function.Injective f) [NeZero N] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {e : ℕ} (χ : DirichletCharacter O N) :
    GD Ω K l e (chHom f χ) ↔ GD Ω K l e χ := by
  have hinj := chHom_inj (N := N) f hf
  have hord : orderOf (chHom f χ) = orderOf χ := orderOf_injective _ hinj χ
  have hine : HV.comp l (chHom f χ) ^ 2 = 1 ↔ HV.comp l χ ^ 2 = 1 := by
    rw [← chHom_comp, ← map_pow]
    exact map_eq_one_iff _ hinj
  have hpar : PsiEven e (chHom f χ) ↔ PsiEven e χ := by
    simp only [PsiEven, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply]
    rw [show ((-1 : O') ^ e) = f ((-1) ^ e) by simp, hf.eq_iff]
  have hker : ∀ ψ : DirichletCharacter O N, (Chr.dirG ℚ Ω (chHom f ψ)).ker = (Chr.dirG ℚ Ω ψ).ker := by
    intro ψ
    ext σ
    simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply]
    rw [Units.ext_iff, Units.ext_iff]
    simp only [MulChar.coe_toUnitHom, chHom, MonoidHom.coe_mk, OneHom.coe_mk, MulChar.ringHomComp_apply,
      Units.val_one]
    exact ⟨fun h => hf (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  constructor
  · intro h
    have heta := h.eta
    rw [← chHom_chiP f hf, hker] at heta
    exact ⟨h.l_odd, h.e_pos, h.N_even, by rw [← hord]; exact h.ord, hine.1 h.ine, hpar.1 h.par, h.quad, h.imag,
      h.l_cop, h.cop, heta, h.gen⟩
  · intro h
    have heta := h.eta
    rw [← hker, chHom_chiP f hf] at heta
    exact ⟨h.l_odd, h.e_pos, h.N_even, by rw [hord]; exact h.ord, hine.2 h.ine, hpar.2 h.par, h.quad, h.imag,
      h.l_cop, h.cop, heta, h.gen⟩

end Transfer

private theorem exists_unram {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (h : ¬ l ∣ orderOf ψ) : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
  have hn : orderOf ψ ≠ 0 := by
    intro h0
    exact h (h0 ▸ dvd_zero l)
  haveI : NeZero (orderOf ψ) := ⟨hn⟩
  have hl : ¬ l ∣ orderOf ψ := h
  obtain ⟨c', hc'e, hroots⟩ := (coefSup l).2.1 (orderOf ψ) hl
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (↥c'.O) (orderOf ψ)
  have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
    hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
  have mem : ∀ u : (ZMod N)ˣ, (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ∈ c'.O := by
    intro u
    have h1 : (ψ.toUnitHom u) ^ orderOf ψ = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hn, pow_orderOf_eq_one,
        MulChar.one_apply (Units.isUnit u), Units.val_one]
    have h2 : (((ψ.toUnitHom u : c.O) : PadicAlgCl l)) ^ orderOf ψ = 1 := by
      have h3 := congrArg (fun y : c.Oˣ => (((y : c.O)) : PadicAlgCl l)) h1
      simpa using h3
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h2
    rw [← hi]
    exact pow_mem ζ.2 i
  let g : (ZMod N)ˣ →* (↥c'.O)ˣ :=
    { toFun := fun u => ⟨⟨_, mem u⟩, ⟨_, mem u⁻¹⟩, by
          apply Subtype.ext
          simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
          rw [← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
            OneMemClass.coe_one], by
          apply Subtype.ext
          simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
          rw [← MulMemClass.coe_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
            OneMemClass.coe_one]⟩
      map_one' := by
        apply Units.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Units.ext
        apply Subtype.ext
        simp }
  refine ⟨c', MulChar.ofUnitHom g, hc'e, fun a => ?_⟩
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [MulChar.ofUnitHom_coe]
    simp [g, MulChar.coe_toUnitHom]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]
    simp

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ]
    (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

private theorem trace_reducible_three_dim {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    (r0 η Ψ g).mat.trace = (Ψ g : R) + 1 + (((Ψ g)⁻¹ : Rˣ) : R) := by
  simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]
