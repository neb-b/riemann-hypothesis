module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.bchiFacts :
    ∀ (h : Host) (t : ℕ), h.Big t → (∀ l ∈ Bchi h.chi, l < h.q1 ∧ l < h.d) ∧ pK h.chi ∈ Bchi h.chi ∧ ¬ pK h.chi ∣ h.N ∧ ¬ pOne h.chi ∣ h.N ∧
      ∀ l, l.Prime → l ≠ 2 → l ∉ Bchi h.chi → 5 ≤ l ∧ ¬ l ∣ h.o ∧ ¬ l ∣ h.q ∧ l ≠ pK h.chi ∧ ¬ l ∣ hStar h.chi ∧ l ≠ pOne h.chi ∧
        ¬ l ∣ h.H.index ∧ ∀ e, 0 < e → e < t → l - 1 ∣ 2 * e → 2 ≤ e ∧ l ≤ 2 * t ∧ ¬ l ∣ h.N := by
  intro h t hB
  obtain ⟨ht1, ht2, hy⟩ := hB
  obtain ⟨hidx, -, -, ho, -, hNp, -⟩ := hostIndex h
  obtain ⟨⟨hKp, -, hK7, hKc⟩, ⟨hOp, -, hOc⟩, -⟩ := pK_pOne_prime_conditions h.chi
  have eq : h.q = h.chi.N := rfl
  have eo : h.o = ordC h.chi := rfl
  obtain ⟨yq1, yqd⟩ := hy h.q (by simp)
  obtain ⟨yo1, yod⟩ := hy h.o (by simp)
  obtain ⟨yK1, yKd⟩ := hy (pK h.chi) (by simp)
  obtain ⟨yS1, ySd⟩ := hy (hStar h.chi) (by simp)
  obtain ⟨yO1, yOd⟩ := hy (pOne h.chi) (by simp)
  have hS0 : hStar h.chi ≠ 0 := (NumberField.classNumber_pos (K := Kstar (pK h.chi))).ne'
  have hq0 : h.chi.N ≠ 0 := h.chi.ne.out
  have hP0 : ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨ho.ne', hq0⟩, hKp.ne_zero⟩, hS0⟩, hOp.ne_zero⟩
  have memB : ∀ l, l.Prime → l ≠ 2 → l ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi →
      l ∈ Bchi h.chi := by
    intro l hl hl2 hlP
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors]
    exact Or.inr ⟨hl2, hl, hlP, hP0⟩
  have dO : ordC h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _
  have dq : h.chi.N ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _
  have dK : pK h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    ((dvd_mul_left _ _).mul_right _).mul_right _
  have dS : hStar h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (dvd_mul_left _ _).mul_right _
  have dO1 : pOne h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    dvd_mul_left _ _
  refine ⟨?_, memB _ hKp (by omega) dK, ?_, ?_, ?_⟩
  · intro l hl
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors] at hl
    rcases hl with rfl | ⟨-, hlp, hlP, -⟩
    · exact ⟨by omega, by omega⟩
    · have le : ∀ y, y ≠ 0 → l ∣ y → l ≤ y := fun y hy0 hly => Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) hly
      rcases hlp.dvd_mul.mp hlP with h4 | h5
      · rcases hlp.dvd_mul.mp h4 with h3 | hS
        · rcases hlp.dvd_mul.mp h3 with h2 | hK
          · rcases hlp.dvd_mul.mp h2 with hO | hQ
            · have := le _ ho.ne' hO
              exact ⟨by omega, by omega⟩
            · have := le _ hq0 hQ
              exact ⟨by omega, by omega⟩
          · have := le _ hKp.ne_zero hK
            exact ⟨by omega, by omega⟩
        · have := le _ hS0 hS
          exact ⟨by omega, by omega⟩
      · have := le _ hOp.ne_zero h5
        exact ⟨by omega, by omega⟩
  · intro hd'
    rcases (hNp _ hKp).mp hd' with h2 | hq' | h1 | h1
    · omega
    · exact (Nat.Prime.coprime_iff_not_dvd hKp).mp hKc hq'
    · omega
    · omega
  · intro hd'
    have nd := (Nat.Prime.coprime_iff_not_dvd hOp).mp hOc
    rcases (hNp _ hOp).mp hd' with h2 | hq' | h1 | h1
    · exact nd (by rw [h2]; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
    · exact nd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq' 2) _)
    · omega
    · omega
  · intro l hl hl2 hlB
    have h3 : l ≠ 3 := by
      intro e
      subst e
      exact hlB (Finset.mem_insert_self _ _)
    have h5 : 5 ≤ l := by
      by_contra hc
      have := hl.two_le
      interval_cases l
      · exact hl2 rfl
      · exact h3 rfl
      · norm_num at hl
    have nd : ∀ y, y ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi → ¬ l ∣ y :=
      fun y hy hly => hlB (memB l hl hl2 (hly.trans hy))
    refine ⟨h5, nd _ dO, nd _ dq, fun e => nd _ dK (by rw [e]), nd _ dS, fun e => nd _ dO1 (by rw [e]), ?_, ?_⟩
    · intro hi
      rcases hl.dvd_mul.mp (hi.trans hidx) with h2 | hO
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h2))
      · exact nd _ dO hO
    · intro e he0 het hle
      have hl1 : l - 1 ≤ 2 * e := Nat.le_of_dvd (by omega) hle
      refine ⟨by omega, by omega, fun hN => ?_⟩
      rcases (hNp l hl).mp hN with h2 | hq' | h1 | h1
      · exact hl2 h2
      · exact nd _ dq hq'
      · omega
      · omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefIndep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem enat_cmp {a a' x x' : ℕ∞} (h : a' * x = a * x') (hx : x ≠ 0) (hx' : x' ≠ 0) (tx : x ≠ ⊤) (tx' : x' ≠ ⊤) :
    (a = ⊤ ↔ a' = ⊤) ∧ (a.toNat : ℝ) / (x.toNat : ℝ) = (a'.toNat : ℝ) / (x'.toNat : ℝ) := by
  lift x to ℕ using tx
  lift x' to ℕ using tx'
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (fun h0 => hx (by simp [h0]))
  have hx0' : (x' : ℝ) ≠ 0 := by exact_mod_cast (fun h0 => hx' (by simp [h0]))
  induction a using ENat.recTopCoe with
  | top =>
    induction a' using ENat.recTopCoe with
    | top => simp
    | coe b =>
      exfalso
      rw [ENat.top_mul hx'] at h
      exact ENat.coe_ne_top _ (by exact_mod_cast h)
  | coe a =>
    induction a' using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.top_mul hx] at h
      exact ENat.coe_ne_top _ (by exact_mod_cast h.symm)
    | coe b =>
      have h' : b * x = a * x' := by exact_mod_cast h
      refine ⟨by simp, ?_⟩
      simp only [ENat.toNat_coe]
      rw [div_eq_div_iff hx0 hx0']
      exact_mod_cast h'.symm

private theorem eO_ne {l : ℕ} [Fact l.Prime] (c : Coef l) : eO l c.O ≠ 0 ∧ eO l c.O ≠ ⊤ := by
  obtain ⟨-, -, -, -, -, h0, hle, -⟩ := dvrFacts l c.O
  exact ⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hle⟩

private theorem coef_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c c' : Coef l)
    (hle : c.O ≤ c'.O) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (ψ' : DirichletCharacter c'.O N)
    (hψ : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l)) :
    (Vlen Ω c e ψ = ⊤ ↔ Vlen Ω c' e ψ' = ⊤) ∧ Vn Ω c e ψ = Vn Ω c' e ψ' := by
  haveI := c.dvr
  haveI := c'.dvr
  haveI := c.fin
  haveI := c'.fin
  letI : Algebra c.O c'.O := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  have hcoe : ∀ y : c.O, ((algebraMap c.O c'.O y : c'.O) : PadicAlgCl l) = (y : PadicAlgCl l) := fun y => rfl
  set θ : Formalism.ConjugateSelfDual.G ℚ Ω →* c.O ˣ := (Chr.dirG ℚ Ω ψ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)) with hθ
  obtain ⟨hq, -⟩ := qoExt l (Formalism.ConjugateSelfDual.G ℚ Ω) c.O c'.O θ ⊤ (shaFam ℚ Ω (l * N))
  have hmap : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)).comp θ
      = (Chr.dirG ℚ Ω ψ')⁻¹ * chiO ℚ Ω l c'.O ^ (-(e : ℤ)) := by
    ext g
    have h1 : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)) (Chr.dirG ℚ Ω ψ g) = Chr.dirG ℚ Ω ψ' g := by
      apply Units.ext
      apply Subtype.ext
      simp only [Units.coe_map, MonoidHom.coe_coe, hcoe]
      exact hψ _
    have h2 : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)) (chiO ℚ Ω l c.O g) = chiO ℚ Ω l c'.O g := by
      apply Units.ext
      simp only [chiO, Units.coe_map, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe]
      exact (IsScalarTower.algebraMap_apply ℤ_[l] c.O c'.O _).symm
    simp only [hθ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, map_mul, map_inv, map_zpow, h1, h2]
  erw [hmap] at hq
  exact enat_cmp hq (eO_ne c).1 (eO_ne c').1 (eO_ne c).2 (eO_ne c').2

theorem UpperTheory.V.HV.coefIndep :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c c' : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (ψ' : DirichletCharacter c'.O N),
      (∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l)) →
      (Vlen Ω c e ψ = ⊤ ↔ Vlen Ω c' e ψ' = ⊤) ∧ Vn Ω c e ψ = Vn Ω c' e ψ' := by
  intro Ω _ _ _ l _ c c' N _ e ψ ψ' h
  obtain ⟨c'', h1, h2⟩ := (coefSup l).1 c c'
  let ψ'' : DirichletCharacter c''.O N := ψ.ringHomComp (Subalgebra.inclusion h1).toRingHom
  obtain ⟨a1, b1⟩ := coef_le Ω l c c'' h1 N e ψ ψ'' fun _ => rfl
  obtain ⟨a2, b2⟩ := coef_le Ω l c' c'' h2 N e ψ' ψ'' fun a => (h a).symm
  exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem cond_dvd_iff {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) {M : ℕ} (h : M ∣ N) :
    ψ.conductor ∣ M ↔ ∀ u, ZMod.unitsMap h u = 1 → ψ.toUnitHom u = 1 := by
  rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ h, DirichletCharacter.mem_conductorSet_iff,
    DirichletCharacter.factorsThrough_iff_ker_unitsMap h]
  rfl

private theorem comp_hom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  unfold comp
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.apply_symm_apply]
  rfl

private theorem mul_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ).toUnitHom u = χ.toUnitHom u * ψ.toUnitHom u := by
  ext
  simp

private theorem rest_hom {O : Type} [CommRing O] {N : ℕ} (χ ψ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (χ * ψ⁻¹).toUnitHom u * ψ.toUnitHom u = χ.toUnitHom u := by
  rw [← mul_hom, inv_mul_cancel_right]

private theorem split_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {r : ℕ} (hr : r.Prime) :
    (comp r χ).conductor = ordProj[r] χ.conductor ∧ (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor := by
  obtain ⟨-, -, hid, -, -, hra, hke, -, hnat⟩ := projFacts N r hr
  have hc := (cond_dvd_iff χ χ.conductor_dvd_level).1 dvd_rfl
  have hc' : ∀ u, ZMod.unitsMap χ.conductor_dvd_level u = 1 → (comp r χ).toUnitHom u = 1 := by
    intro u hu
    rw [comp_hom]
    apply hc
    rw [hnat, hu, map_one]
  have ha1 : (comp r χ).conductor ∣ χ.conductor := (cond_dvd_iff _ χ.conductor_dvd_level).2 hc'
  have hb1 : (χ * (comp r χ)⁻¹).conductor ∣ χ.conductor := by
    refine (cond_dvd_iff _ χ.conductor_dvd_level).2 fun u hu => ?_
    have := rest_hom χ (comp r χ) u
    rwa [hc u hu, hc' u hu, mul_one] at this
  have ha2 : (comp r χ).conductor ∣ ordProj[r] N := by
    refine (cond_dvd_iff _ (Nat.ordProj_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).ker := by rw [hke]; exact hu
    rw [comp_hom, MonoidHom.mem_ker.1 this, map_one]
  have hb2 : (χ * (comp r χ)⁻¹).conductor ∣ ordCompl[r] N := by
    refine (cond_dvd_iff _ (Nat.ordCompl_dvd N r)).2 fun u hu => ?_
    have : u ∈ (proj r N).range := by rw [hra]; exact hu
    obtain ⟨v, rfl⟩ := this
    have := rest_hom χ (comp r χ) (proj r N v)
    rw [comp_hom, hid] at this
    exact mul_eq_right.1 this
  have hcop : (comp r χ).conductor.Coprime (χ * (comp r χ)⁻¹).conductor :=
    ((coprime_ordProj_ordCompl r N).coprime_dvd_left ha2).coprime_dvd_right hb2
  have h1 := hcop.mul_dvd_of_dvd_of_dvd ha1 hb1
  have h2 : χ.conductor ∣ (comp r χ).conductor * (χ * (comp r χ)⁻¹).conductor := by
    have hN := h1.trans χ.conductor_dvd_level
    refine (cond_dvd_iff _ hN).2 fun u hu => ?_
    have e1 := (cond_dvd_iff _ hN).1 (dvd_mul_right _ _) u hu
    have e2 := (cond_dvd_iff _ hN).1 (dvd_mul_left _ _) u hu
    rw [← rest_hom χ (comp r χ) u, e1, e2, mul_one]
  have he := h2.antisymm h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 ha2
  have hb3 : ¬ r ∣ (χ * (comp r χ)⁻¹).conductor := fun h =>
    Nat.not_dvd_ordCompl hr (NeZero.ne N) (h.trans hb2)
  have hb0 := (χ * (comp r χ)⁻¹).conductor_ne_zero
  have hf : χ.conductor.factorization r = k := by
    rw [he, hk, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) hb0]
    simp [hr.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hb3]
  rw [hf]
  refine ⟨hk, ?_⟩
  rw [hk] at he
  exact (Nat.div_eq_of_eq_mul_right (pow_pos hr.pos k) he).symm

theorem UpperTheory.V.HV.compCond :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      (comp r χ).conductor = ordProj[r] χ.conductor ∧ (comp r χ = 1 ↔ ¬ r ∣ χ.conductor) ∧
      (χ * (comp r χ)⁻¹).conductor = ordCompl[r] χ.conductor ∧ 2 ^ c2 χ = (psi2 χ).conductor ∧ 2 ^ c2 χ ∣ N ∧
      ∀ (M : ℕ), M ∣ N → (χ.conductor ∣ M ↔ ∀ p ∈ N.primeFactors, (comp p χ).conductor ∣ M) := by
  intro O _ _ N _ χ r hr
  have h2 : 2 ^ c2 χ = (psi2 χ).conductor := by
    unfold c2 psi2
    rw [(split_cond χ Nat.prime_two).1, Nat.prime_two.factorization_pow]
    simp
  refine ⟨(split_cond χ hr).1, ?_, (split_cond χ hr).2, h2, h2 ▸ (psi2 χ).conductor_dvd_level, fun M _ => ⟨fun h p hp => ?_, fun h => ?_⟩⟩
  · rw [DirichletCharacter.eq_one_iff_conductor_eq_one, (split_cond χ hr).1,
      hr.dvd_iff_one_le_factorization χ.conductor_ne_zero, Nat.pow_eq_one]
    have := hr.one_lt
    omega
  · rw [(split_cond χ (Nat.prime_of_mem_primeFactors hp)).1]
    exact (Nat.ordProj_dvd _ _).trans h
  · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hpN : p ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hp, ((dvd_pow_self p hk0.ne').trans hk).trans χ.conductor_dvd_level, NeZero.ne N⟩
      have := h p hpN
      rw [(split_cond χ hp).1] at this
      exact (pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization χ.conductor_ne_zero).1 hk)).trans this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem compIne_map (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) :
    (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI hMz : NeZero (N / r ^ N.factorization r) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hMcop : (N / r ^ N.factorization r).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have fix : ∀ σ ∈ Ine (F := ℚ) A, ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 → σ ζ = ζ :=
    fun σ hσ ζ hζ => (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hMcop ζ hζ).2 σ hσ
  have powOne : ∀ ζ : Ω, ζ ^ (N / r ^ N.factorization r) = 1 →
      ζ ^ (((1 : (ZMod (N / r ^ N.factorization r))ˣ) : ZMod (N / r ^ N.factorization r))).val = ζ := by
    intro ζ hζ
    rw [Units.val_one, ZMod.val_one_eq_one_mod]
    by_cases h1 : N / r ^ N.factorization r = 1
    · rw [h1, pow_one] at hζ
      rw [hζ, one_pow]
    · rw [Nat.mod_eq_of_lt (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hMz.out, h1⟩), pow_one]
  have kerCls : ∀ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω (N / r ^ N.factorization r) σ = 1 := fun σ hσ =>
    (Chr.clsFacts ℚ Ω _).2.2.1 σ 1 (fun ζ hζ => by rw [fix σ hσ ζ hζ, powOne ζ hζ])
  ext u
  rw [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have e := congrArg (fun f => f σ) ((Chr.clsFacts ℚ Ω N).2.1 _ (Nat.ordCompl_dvd N r))
    simp only [MonoidHom.comp_apply] at e
    rw [e]
    exact kerCls σ hσ
  · intro hu
    obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
    refine ⟨σ, hσ, ?_⟩
    apply (Chr.clsFacts ℚ Ω N).2.2.1
    refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).mpr ⟨?_, ?_⟩
    · intro ζ hζ
      rw [hu, powOne ζ hζ]
      exact fix σ hσ ζ hζ
    · rw [← hv, ← hσv]
      rfl

private theorem compIne_unit {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) :
    (comp r χ).toUnitHom = χ.toUnitHom.comp (proj r N) := by
  ext u
  simp [UpperTheory.V.HV.comp]

theorem UpperTheory.V.HV.compIne :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ), r.Prime → ∀ A : ValuationSubring Ω, A.valuation (r : Ω) < 1 →
      (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] (χ : DirichletCharacter O N), (∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ) ∧
        (Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω χ).ker ↔ comp r χ = 1) := by
  intro Ω _ _ _ N _ r hr A hA
  have hrange : (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) = (proj r N).range := by
    rw [compIne_map Ω N r hr A hA, (projFacts N r hr).2.2.2.2.2.1]
  refine ⟨hrange, fun O _ _ χ => ?_⟩
  have same : ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω χ σ = Chr.dirG ℚ Ω (comp r χ) σ := by
    intro σ hσ
    have hm : Chr.cls ℚ Ω N σ ∈ (proj r N).range := by
      rw [← hrange]
      exact Subgroup.mem_map_of_mem _ hσ
    obtain ⟨w, hw⟩ := hm
    simp only [Chr.dirG, MonoidHom.comp_apply, compIne_unit]
    rw [← hw, (projFacts N r hr).2.2.1 w]
  refine ⟨same, ⟨fun h => ?_, fun h σ hσ => ?_⟩⟩
  · rw [MulChar.eq_one_iff]
    intro u
    have hm : proj r N u ∈ (Ine (F := ℚ) A).map (Chr.cls ℚ Ω N) := by
      rw [hrange]
      exact ⟨u, rfl⟩
    obtain ⟨σ, hσ, hσu⟩ := hm
    have h1 := h hσ
    rw [MonoidHom.mem_ker] at h1
    simp only [Chr.dirG, MonoidHom.comp_apply] at h1
    rw [← MulChar.coe_toUnitHom, compIne_unit, MonoidHom.comp_apply, ← hσu, h1, Units.val_one]
  · rw [MonoidHom.mem_ker, same σ hσ]
    simp only [Chr.dirG, MonoidHom.comp_apply, h]
    ext
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CongrFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

section Loc

variable {O : Type} [CommRing O] [IsLocalRing O]

private theorem sub_mem_iff (x y : O) :
    x - y ∈ IsLocalRing.maximalIdeal O ↔ IsLocalRing.residue O x = IsLocalRing.residue O y := by
  exact (Ideal.Quotient.eq).symm

private theorem res_eq_one (l : ℕ) [hl : Fact l.Prime] (h : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hx : x ^ l ^ s = 1) :
    IsLocalRing.residue O x = 1 := by
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact h
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 : (IsLocalRing.residue O x - 1) ^ l ^ s = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hx, map_one, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero s hl.out.ne_zero) |>.1 h1)

private theorem eq_of_res_eq [IsDomain O] (x y : Oˣ) (m : ℕ) (hm : IsUnit (m : O)) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  have hw : (x * y⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have hr : IsLocalRing.residue O ((x * y⁻¹ : Oˣ) : O) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hzm : ((x * y⁻¹ : Oˣ) : O) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hs : IsUnit (∑ i ∈ Finset.range m, ((x * y⁻¹ : Oˣ) : O) ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (IsLocalRing.residue O) m]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hm
  have e := geom_sum_mul ((x * y⁻¹ : Oˣ) : O) m
  rw [hzm, sub_self] at e
  have hz1 := (hs.mul_right_eq_zero).mp e
  have h1 : x * y⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp hz1)
  exact mul_inv_eq_one.mp h1

private theorem res_inv (x : Oˣ) : IsLocalRing.residue O ((x⁻¹ : Oˣ) : O) = (IsLocalRing.residue O x)⁻¹ := by
  exact map_units_inv (IsLocalRing.residue O) x

end Loc

theorem UpperTheory.V.HV.congrFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), Equivalence (Congr (Ω := Ω) c) ∧
      (∀ a a' b b' : G ℚ Ω →* c.Oˣ, Congr c a a' → Congr c b b' → Congr c (a * b) (a' * b') ∧ Congr c a⁻¹ a'⁻¹) ∧
      (∀ (a : G ℚ Ω →* c.Oˣ) (s : ℕ), a ^ l ^ s = 1 → Congr c a 1) ∧
      (∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 → (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y) ∧
      ∀ (a b : G ℚ Ω →* c.Oˣ) (m : ℕ), ¬ l ∣ m → a ^ m = 1 → b ^ m = 1 → Congr c a b → a = b := by
  intro Ω _ _ _ l _ c
  haveI := c.dvr
  haveI := c.fin
  have hF := dvrFacts l c.O
  have hlu : ¬ IsUnit ((l : ℕ) : c.O) := by
    intro hu
    have hu' : IsUnit (algebraMap ℤ_[l] c.O ((l : ℕ) : ℤ_[l])) := by rwa [map_natCast]
    haveI := hF.2.2.1
    exact PadicInt.p_nonunit (IsLocalHom.map_nonunit _ hu')
  have cr : ∀ a b : G ℚ Ω →* c.Oˣ, Congr c a b ↔
      ∀ σ, IsLocalRing.residue c.O (a σ : c.O) = IsLocalRing.residue c.O (b σ : c.O) :=
    fun a b => forall_congr' fun σ => sub_mem_iff _ _
  have p4 : ∀ (x y : c.Oˣ) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → y ^ m = 1 →
      (x : c.O) - y ∈ IsLocalRing.maximalIdeal c.O → x = y :=
    fun x y m hm hx hy hxy => eq_of_res_eq x y m (hF.2.2.2.2.2.2.2.2 m hm) hx hy ((sub_mem_iff _ _).mp hxy)
  have papp : ∀ (a : G ℚ Ω →* c.Oˣ) (n : ℕ), a ^ n = 1 → ∀ σ, (a σ) ^ n = 1 := by
    intro a n ha σ
    rw [← MonoidHom.pow_apply, ha, MonoidHom.one_apply]
  refine ⟨⟨fun a => ?_, fun {a b} h => ?_, fun {a b d} h1 h2 => ?_⟩, fun a a' b b' ha hb => ⟨?_, ?_⟩,
    fun a s ha => ?_, p4, fun a b m hm ha hb hab => ?_⟩
  · rw [cr]
    intro σ
    rfl
  · rw [cr] at h ⊢
    intro σ
    exact (h σ).symm
  · rw [cr] at h1 h2 ⊢
    intro σ
    exact (h1 σ).trans (h2 σ)
  · rw [cr] at ha hb ⊢
    intro σ
    simp only [MonoidHom.mul_apply, Units.val_mul, map_mul, ha σ, hb σ]
  · rw [cr] at ha ⊢
    intro σ
    simp only [MonoidHom.inv_apply, res_inv, ha σ]
  · rw [cr]
    intro σ
    have e' : ((a σ : c.O)) ^ l ^ s = 1 := by
      rw [← Units.val_pow_eq_pow_val, papp a _ ha σ, Units.val_one]
    rw [res_eq_one l hlu _ s e', MonoidHom.one_apply, Units.val_one, map_one]
  · apply MonoidHom.ext
    intro σ
    exact p4 _ _ m hm (papp a m ha σ) (papp b m hb σ) (hab σ)
end

