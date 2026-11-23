module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RingEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ModelUpper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transfer

variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')

private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f

private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf

private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl

private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  have h : chHom f (th0 l χ) = th0 l (chHom f χ) := by
    simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, orderOf_injective _ (chHom_inj f hf)]
  simp only [chiP, map_mul, map_inv, chHom_comp, h]

private theorem gd_chHom (hf : Function.Injective f) [NeZero N] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {e : ℕ} (χ : DirichletCharacter O N) :
    GD Ω K l e (chHom f χ) ↔ GD Ω K l e χ := by
  have h1 : orderOf (chHom f χ) = orderOf χ := orderOf_injective _ (chHom_inj f hf) _
  have h2 : comp l (chHom f χ) ^ 2 = 1 ↔ comp l χ ^ 2 = 1 := by
    rw [← chHom_comp, ← map_pow, map_eq_one_iff _ (chHom_inj f hf)]
  have h3 : PsiEven e (chHom f χ) ↔ PsiEven e χ := by
    show f (χ (-1)) = _ ↔ χ (-1) = _
    rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]
  have h4 : (Chr.dirG ℚ Ω (chiP l (chHom f χ))).ker = (Chr.dirG ℚ Ω (chiP l χ)).ker := by
    rw [← chHom_chiP f hf]
    ext g
    simp only [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    exact map_eq_one_iff f hf
  exact ⟨fun h => ⟨h.l_odd, h.e_pos, h.N_even, h1 ▸ h.ord, h2.1 h.ine, h3.1 h.par, h.quad, h.imag, h.l_cop, h.cop,
      h4 ▸ h.eta, h.gen⟩,
    fun h => ⟨h.l_odd, h.e_pos, h.N_even, h1 ▸ h.ord, h2.2 h.ine, h3.2 h.par, h.quad, h.imag, h.l_cop, h.cop,
      h4 ▸ h.eta, h.gen⟩⟩

end Transfer

private theorem exists_unram {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (h : ¬ l ∣ orderOf ψ) : ∃ (c' : Coef l) (ψ' : DirichletCharacter c'.O N), eO l c'.O = 1 ∧
      ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l) := by
  haveI : NeZero (orderOf ψ) := ⟨fun h0 => h (h0 ▸ dvd_zero l)⟩
  obtain ⟨c', he, hr⟩ := (coefSup l).2.1 (orderOf ψ) h
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c'.O (orderOf ψ)
  have hζ' : IsPrimitiveRoot (ζ : PadicAlgCl l) (orderOf ψ) :=
    hζ.map_of_injective (f := c'.O.val) Subtype.val_injective
  have hmem : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) ∈ c'.O := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      have h1 : ψ u ^ orderOf ψ = 1 := by
        rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
      have h2 : ((ψ u : c.O) : PadicAlgCl l) ^ orderOf ψ = 1 := by
        rw [← SubmonoidClass.coe_pow, h1]; rfl
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h2
      rw [← hi]
      exact pow_mem ζ.2 i
    · rw [ψ.map_nonunit ha]
      exact zero_mem _
  refine ⟨c', ⟨⟨⟨fun a => ⟨_, hmem a⟩, Subtype.ext ?_⟩, fun a b => Subtype.ext ?_⟩, fun a ha => Subtype.ext ?_⟩, he,
    fun _ => rfl⟩
  · show ((ψ 1 : c.O) : PadicAlgCl l) = 1
    rw [map_one]; rfl
  · show ((ψ (a * b) : c.O) : PadicAlgCl l) = _
    rw [map_mul]; rfl
  · show ((ψ a : c.O) : PadicAlgCl l) = 0
    rw [ψ.map_nonunit ha]; rfl

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ]
    (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

private theorem trace_reducible_three_dim {Γ R : Type} [Group Γ] [CommRing R] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) :
    (r0 η Ψ g).mat.trace = (Ψ g : R) + 1 + (((Ψ g)⁻¹ : Rˣ) : R) := by
  simp [GG.mat, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three, wt1]
