module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem opP_mul' (δ : G ℚ Ω) (a : ℕ) (x y : Ω) : opP δ a (x * y) = opP δ a x * opP δ a y := by
  simp only [opP, map_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

private theorem opP_ne' (δ : G ℚ Ω) (a : ℕ) {x : Ω} (hx : x ≠ 0) : opP δ a x ≠ 0 :=
  div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)

private theorem opP_eq' {M a : ℕ} (hM : M ≠ 0) {δ : G ℚ Ω} (hδ : Pows M a δ) {x y : Ω} (hy : y ^ M ≠ 0)
    (h : x ^ M = y ^ M) : opP δ a x = opP δ a y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hy
    exact hy rfl
  have hw : (x / y) ^ M = 1 := by rw [div_pow, h, div_self hy]
  have hw0 : x / y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hw
    exact zero_ne_one hw
  have hx : x = y * (x / y) := (mul_div_cancel₀ x hy0).symm
  have h1 : opP δ a (x / y) = 1 := by
    unfold opP
    rw [hδ _ hw, div_self (pow_ne_zero _ hw0)]
  rw [hx, opP_mul', h1, mul_one]

private theorem zeta_inj' {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) {i j k : ZMod M}
    (h : ζ ^ i.val = ζ ^ j.val * ζ ^ k.val) : i = j + k := by
  rw [← pow_add] at h
  have h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val) := by
    rw [ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))

end

theorem UpperTheory.V.ML.kolHom :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) ∧ IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) ∧
    ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
  intro Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK
  have hM : M ≠ 0 := NeZero.ne M
  have gb := galBasic Ω (F * n) hFn
  have gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F := gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)
  obtain ⟨Y₀, hY₀, hK'⟩ := hK
  have hgy : ∀ g : G ℚ Ω, g y / y ≠ 0 := fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy
  have hY0 : Y₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hY₀
    exact hy hY₀.symm
  have hA : opP δ a Y₀ ≠ 0 := opP_ne' δ a hY0
  have key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro Y hY g hg z hz
    obtain ⟨z₀, -, hz₀, hκ⟩ := hK' g hg
    have e1 : opP δ a Y = opP δ a Y₀ :=
      opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)
    have e2 : opP δ a z = opP δ a z₀ :=
      opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)
    rw [e1, e2]
    exact hκ
  have hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v := by
    intro u hu v hv
    obtain ⟨zu, -, hzu, hκu⟩ := hK' u hu
    obtain ⟨zv, hzvfix, hzv, hκv⟩ := hK' v hv
    have hzu0 : zu ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzu
      exact hgy u hzu.symm
    have hzv0 : zv ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzv
      exact hgy v hzv.symm
    have huy : u y ≠ 0 := (map_ne_zero u).mpr hy
    have hz : (u zv * zu) ^ M = (u * v) y / y := by
      rw [mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]
      field_simp
    have euv := key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz
    have hcomm : δ (u zv) = u (δ zv) := gb.2.2.2.2.2.1 zv hzvfix δ u
    have hPu : opP δ a (u zv) = u (opP δ a zv) := by
      unfold opP
      rw [hcomm, map_div₀, map_pow]
    rw [opP_mul', hPu, AlgEquiv.mul_apply] at euv
    have hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val := by
      apply hu
      obtain ⟨c, hc⟩ := hMF
      rw [hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow,
        one_pow]
    have ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv) := by
      rw [← hfixζ, hκv, map_div₀, map_div₀]
    have hB : opP δ a zu ≠ 0 := opP_ne' δ a hzu0
    have huA : u (opP δ a Y₀) ≠ 0 := (map_ne_zero u).mpr hA
    have huC : u (opP δ a zv) ≠ 0 := (map_ne_zero u).mpr (opP_ne' δ a hzv0)
    apply zeta_inj' hζ
    rw [euv, hκu, ev']
    field_simp
  refine ⟨hmul, ?_, key⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ (opP δ a Y₀) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  let H : Set (G ℚ Ω) := (fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩
    ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))
  have hHo : IsOpen H := gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hH0 : ∀ h ∈ H, κ h = 0 := by
    rintro h ⟨h1, h2⟩
    have e := key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])
    have hP1 : opP δ a (1 : Ω) = 1 := by simp [opP]
    have hfx : h (opP δ a Y₀) = opP δ a Y₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    rw [hP1, hfx, div_self hA, div_one] at e
    have e0 := zeta_inj' hζ (i := κ h) (j := 0) (k := 0)
      (by rw [e, ZMod.val_zero, pow_zero, one_mul])
    simpa using e0
  have hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_subtype_val)
  have hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} := by
    show (x : G ℚ Ω)⁻¹ * x ∈ H
    rw [inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  filter_upwards [hS.mem_nhds hx] with w hw
  have hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F := gbF hw.1
  have e := hmul x x.2 _ hw'
  rw [mul_inv_cancel_left, hH0 _ hw, add_zero] at e
  exact e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShtNu
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.shtNu :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → ∀ δ : G ℚ Ω, IsUnit ((α δ : O) - 1) → ∀ a : O, a ∣ (l : O) ^ m → ∀ c ∈ ShT (QO l O) α δ F a,
    IsNu (l ^ m) F F α c ∧ ((∀ u ∈ fixMu ℚ Ω F, c u = 0) → c = 0) ∧
    ∀ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime → q ≡ 1 [MOD F] → Over A q → IsFrob (F := ℚ) A q φ → c φ = 0 →
      ∀ A' : ValuationSubring Ω, Over A' q → ∀ g ∈ Dec (F := ℚ) A', c g = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N₀ m F α hD δ hδ a ha c hc
  obtain ⟨⟨hlc, hcoc⟩, hcδ, hac, hunr, -⟩ := hc
  have hkill : ∀ x ∈ fixMu ℚ Ω F, ∀ w : QO l O, a • w = 0 → (α x : O) • w = w := by
    intro x hx w hw
    obtain ⟨t, ht⟩ := hD.triv x hx
    obtain ⟨b, hb⟩ := ha
    have h1 : ((α x : O) - 1) • w = 0 := by
      rw [ht, hb, show a * b * t = (b * t) * a by ring, mul_smul, hw, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at h1
  have h1 : c 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at e
    simpa using e
  have heqv : ∀ g u, u ∈ fixMu ℚ Ω F → c (g * u * g⁻¹) = (α g : O) • c u := by
    intro g u hu
    have e1 := hcoc (g * u) g⁻¹
    have e2 := hcoc g u
    have e3 := hcoc g g⁻¹
    rw [mul_inv_cancel, h1] at e3
    rw [e1, e2, map_mul, Units.val_mul, mul_smul, hkill u hu _ (hac _), add_right_comm, ← e3, zero_add]
  have hF : F ≠ 0 := by
    rw [hD.lev]
    have hl : l.Prime := Fact.out
    have hN : N₀ ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' ((Nat.coprime_zero_left _).mp hD.cop)
    exact mul_ne_zero hN (pow_ne_zero _ hl.ne_zero)
  obtain ⟨-, hopen, hcomm, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u hu v _
    rw [hcoc, hkill u hu _ (hac _)]
  · exact hlc.comp_continuous continuous_subtype_val
  · exact heqv
  · intro u _
    obtain ⟨b, hb⟩ := ha
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hb, mul_comm, mul_smul, hac, smul_zero]
  · exact hunr
  · intro hz
    refine funext fun g => ?_
    have hk := hcomm g δ
    have e : g * δ = (g * δ * g⁻¹ * δ⁻¹) * (δ * g) := by group
    have e1 := hcoc g δ
    rw [hcδ, smul_zero, add_zero, e, hcoc _ (δ * g), hz _ hk, zero_add,
      hkill _ hk _ (hac _), hcoc δ g, hcδ, zero_add] at e1
    have e2 : ((α δ : O) - 1) • c g = 0 := by rw [sub_smul, one_smul, e1, sub_self]
    exact (hδ.smul_eq_zero).mp e2
  · intro q A φ hq hq1 hA hφ hcφ A' hA' x hx
    obtain ⟨-, -, -, hcopNot, hIne, -, hPows, hconj, hplace, hact⟩ := placeBasic Ω
    have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
    have hAF : ¬Over A F := hcopNot A q F hcop hA
    have hφF : φ ∈ fixMu ℚ Ω F := by
      intro y hy
      rw [hPows A q F φ hφ hAF y hy, pow_eq_pow_mod q hy, hq1, ← pow_eq_pow_mod 1 hy, pow_one]
    let K : Subgroup (G ℚ Ω) :=
      { carrier := {g | g ∈ fixMu ℚ Ω F ∧ c g = 0}
        mul_mem' := fun {u v} hu hv =>
          ⟨mul_mem hu.1 hv.1, by rw [hcoc, hu.2, hkill _ hu.1 _ (hac _), hv.2, add_zero]⟩
        one_mem' := ⟨one_mem _, h1⟩
        inv_mem' := fun {u} hu => by
          refine ⟨inv_mem hu.1, ?_⟩
          have e := hcoc u u⁻¹
          rw [mul_inv_cancel, h1, hu.2, zero_add, hkill _ hu.1 _ (hac _)] at e
          exact e.symm }
    have hKo : IsOpen (K : Set (G ℚ Ω)) := hopen.inter (hlc.isOpen_fiber 0)
    have hIK : Ine A ≤ K := fun g hg => ⟨hIne A F hAF hg, hunr A hAF g hg⟩
    obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
    have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
    have hDec : Dec A ≤ K := Kum.decGen ℚ Ω A v φ K hv hfr hKo hIK ⟨hφF, hcφ⟩
    obtain ⟨g, rfl⟩ := hconj A A' q hq hA hA'
    have hy := hDec (((hact A g).1 x).mp hx)
    have ex : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [ex, heqv g _ hy.1, hy.2, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.SysOfLax
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω]

private def Cg (A : ValuationSubring Ω) (u v : Ω) : Prop :=
  A.valuation u = 1 ∧ A.valuation v = 1 ∧ A.valuation (u - v) < 1

private theorem cg_of (A : ValuationSubring Ω) {u v : Ω} (hu : A.valuation u = 1) (h : A.valuation (u - v) < 1) :
    Cg A u v := by
  refine ⟨hu, ?_, h⟩
  have h1 : A.valuation (-(u - v)) < A.valuation u := by rw [Valuation.map_neg, hu]; exact h
  have h2 := A.valuation.map_add_eq_of_lt_left h1
  have h3 : u + -(u - v) = v := by ring
  rw [h3, hu] at h2
  exact h2

private theorem cg_mul {A : ValuationSubring Ω} {u v u' v' : Ω} (h : Cg A u v) (h' : Cg A u' v') :
    Cg A (u * u') (v * v') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], by rw [map_mul, h.2.1, h'.2.1, one_mul], ?_⟩
  have : u * u' - v * v' = u * (u' - v') + (u - v) * v' := by ring
  rw [this]
  refine A.valuation.map_add_lt ?_ ?_
  · rw [map_mul, h.1, one_mul]; exact h'.2.2
  · rw [map_mul, h'.2.1, mul_one]; exact h.2.2

private theorem cg_pow {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) (n : ℕ) : Cg A (u ^ n) (v ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ]; exact cg_mul ih h

private theorem cg_inv {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) : Cg A u⁻¹ v⁻¹ := by
  have hu : u ≠ 0 := fun h0 => by have := h.1; rw [h0, map_zero] at this; exact zero_ne_one this
  have hv : v ≠ 0 := fun h0 => by have := h.2.1; rw [h0, map_zero] at this; exact zero_ne_one this
  refine ⟨by rw [map_inv₀, h.1, inv_one], by rw [map_inv₀, h.2.1, inv_one], ?_⟩
  have : u⁻¹ - v⁻¹ = -((u - v) * u⁻¹ * v⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, h.1, h.2.1, inv_one, mul_one, mul_one]
  exact h.2.2

variable [Algebra ℚ Ω]

private theorem opP_mul (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u * v) = opP δ a u * opP δ a v := by
  simp only [opP, map_mul, mul_pow, mul_div_mul_comm]

private theorem opP_div (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u / v) = opP δ a u / opP δ a v := by
  simp only [opP, map_div₀, div_pow]
  rw [div_div_div_comm]

private theorem opP_pow (δ : G ℚ Ω) (a : ℕ) (u : Ω) (n : ℕ) : opP δ a (u ^ n) = opP δ a u ^ n := by
  simp only [opP, map_pow, div_pow]
  rw [← pow_mul, ← pow_mul, mul_comm]

private theorem map_opP (δ g : G ℚ Ω) (a : ℕ) (u : Ω) (h : g (δ u) = δ (g u)) :
    g (opP δ a u) = opP δ a (g u) := by
  simp only [opP, map_div₀, map_pow, h]

private theorem opP_root (δ : G ℚ Ω) (a N : ℕ) (hN : N ≠ 0) (hδ : Pows N a δ) (ζ : Ω) (h : ζ ^ N = 1) :
    opP δ a ζ = 1 := by
  have h0 : ζ ≠ 0 := fun h0 => by rw [h0, zero_pow hN] at h; exact zero_ne_one h
  rw [opP, hδ ζ h, div_self (pow_ne_zero _ h0)]

private theorem nrm_opP (δ τ : G ℚ Ω) (a q n : ℕ) (u : Ω) (h : ∀ g : G ℚ Ω, g (δ u) = δ (g u)) :
    nrm q τ (opP δ a u ^ n) = opP δ a (nrm q τ u) ^ n := by
  simp only [nrm, map_pow, opP, map_div₀, h, map_prod]
  rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_pow]

end SlopeTestRemainingChoices

private theorem admissible_of_integral_conj_le {l F r q d : ℕ} (h : ML.admitted l F r (q * d)) : ML.admitted l F r d :=
  ⟨h.1.squarefree_of_dvd (Dvd.intro_left q rfl), fun p hp hd => h.2 p hp (hd.mul_left q)⟩

private theorem admissible_prime_coprime {l F r q : ℕ} (h : AdmP l F r q) : q.Coprime r := by
  have hq := h.1
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  haveI : Fact q.Prime := ⟨hq⟩
  apply h.2.2.2
  have : (r : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff r q).2 hd
  rw [this, orderOf_zero]
  exact dvd_zero l

theorem UpperTheory.V.ML.sysOfLax :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l N₀ m F r a : ℕ), l.Prime → l ≠ 2 → N₀.Coprime l → 1 ≤ m → F = N₀ * l ^ m → ∀ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s →
    ∀ δ : G ℚ Ω, Pows (l ^ m) a δ → Sys l F r (fun d => opP δ a (X d) ^ (2 * N₀ * d)) fun d q => q * s d q := by
  intro Ω _ _ _ l N₀ m F r a hl _ hN hm hF X s hX δ hδ
  have hN0 : N₀ ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hN
    exact hl.one_lt.ne' hN
  have hlm : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hF0 : F ≠ 0 := hF ▸ mul_ne_zero hN0 hlm
  have hFd : ∀ d, ML.admitted l F r d → F * d ≠ 0 := fun d hd => mul_ne_zero hF0 hd.1.ne_zero
  have hcomm : ∀ d, ML.admitted l F r d → ∀ g h : G ℚ Ω, g (h (X d)) = h (g (X d)) := fun d hd =>
    (galBasic Ω (F * d) (hFd d hd)).2.2.2.2.2.1 (X d) (hX.fix d hd)
  obtain ⟨-, -, -, hcop, -, -, -, -, -, hact⟩ := placeBasic Ω
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) < 1 ↔ (δ⁻¹ • A).valuation y < 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.1 y
    rwa [smul_inv_smul] at this
  have heq : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) = 1 ↔ (δ⁻¹ • A).valuation y = 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.2 y
    rwa [smul_inv_smul] at this
  have hov : ∀ (A : ValuationSubring Ω) (n : ℕ), Over (δ⁻¹ • A) n ↔ Over A n := fun A n => by
    have := hlt A (n : Ω)
    rw [map_natCast] at this
    exact this.symm
  have hδu : ∀ d, ML.admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (δ (X d)) = 1 :=
    fun d hd A hA => (heq A _).2 (hX.unit d hd _ fun h => hA ((hov A r).1 h))
  have hζ : ∀ (n : ℕ) (ζ : Ω), ζ ^ (2 * F * n) = 1 → opP δ a ζ ^ (2 * N₀ * n) = 1 := fun n ζ h => by
    rw [← opP_pow]
    refine opP_root δ a (l ^ m) hlm hδ _ ?_
    rw [← pow_mul, ← h, hF]
    congr 1
    ring
  refine ⟨fun d hd => ?_, fun d hd g hg => ?_, fun d hd A hA => ?_, fun d q hq hd => ?_,
    fun d q hq hd τ hτ hgen φ hφ => ?_, fun d q hq hd φ hφ A hA => ?_⟩
  · refine pow_ne_zero _ (div_ne_zero ?_ (pow_ne_zero _ (hX.ne d hd)))
    exact (map_ne_zero δ).2 (hX.ne d hd)
  · rw [map_pow, map_opP δ g a _ (hcomm d hd g δ), hX.fix d hd g hg]
  · rw [map_pow, opP, map_div₀, map_pow, hδu d hd A hA, hX.unit d hd A hA]
    simp
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · have h1 := (hd.2 q hq (Dvd.intro d rfl)).2.1
      have hlF : l ∣ F := hF ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N₀
      have h2 : l ∣ 1 := ((h1.of_dvd hlF).dvd_iff dvd_rfl).1 h
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
    · exact hX.cop d q hq hd h
  · obtain ⟨ζ, h1, h2⟩ := hX.norm d q hq hd τ hτ hgen φ hφ
    rw [nrm_opP δ τ a q _ _ (fun g => hcomm _ hd g δ), h2, opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, opP_div,
      map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← div_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · obtain ⟨ζ, h1, h2⟩ := hX.cong d q hq hd φ hφ
    have hr : ¬ Over A r := hcop A q r (admissible_prime_coprime (hd.2 q hq (Dvd.intro d rfl))) hA
    have c1 := cg_of A (hX.unit _ hd A hr) (h2 A hA)
    have h3 := (hlt A _).2 (h2 _ ((hov A q).2 hA))
    rw [map_sub] at h3
    have c2 := cg_of A (hδu _ hd A hr) h3
    have c3 := cg_pow (cg_mul c2 (cg_inv (cg_pow c1 a))) (2 * N₀ * (q * d))
    rw [← div_eq_mul_inv, ← div_eq_mul_inv] at c3
    have c4 : A.valuation (opP δ a (X (q * d)) ^ (2 * N₀ * (q * d)) -
      opP δ a (ζ * φ⁻¹ (X d) ^ s d q) ^ (2 * N₀ * (q * d))) < 1 := c3.2.2
    rw [opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, ← pow_mul] at c4
    rw [map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← pow_mul]
    have e : 2 * N₀ * d * (q * s d q) = s d q * (2 * N₀ * (q * d)) := by ring
    rw [e]
    exact c4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.xEx :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)), b < M → 𝔞 ≠ ⊥ → ∃ X : K, IsX M K b 𝔞 X := by
  intro M _ K _ _ _ b 𝔞 hb h𝔞
  have h𝔞0 : 𝔞 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔞
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}
  have hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  have hS : S.Finite := Ideal.finite_factors hM0
  obtain ⟨v, hvS, hprime, hvc⟩ := degOne K S hS (ClassGroup.mk0 ⟨𝔞, h𝔞0⟩)⁻¹
  haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩
  obtain ⟨π, hπ⟩ := (red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl
  have hpv := ((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2
  have hcop : (Ideal.absNorm v.asIdeal).Coprime M := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    rintro ⟨k, hk⟩
    apply hvS
    show v.asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv
  have hζ := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπζ, hdvd⟩ := redRoot (𝓞 K) _ π M _ hcop hζ
  obtain ⟨χ, hχ, -⟩ := teich (𝓞 K) _ π M ((Ideal.absNorm v.asIdeal - 1) / M) _ hζ hπζ (Nat.mul_div_cancel' hdvd)
  have hXv := xJac M K b _ π χ hcop hb hχ
  rw [hπ] at hXv
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hprin : (𝔞 * v.asIdeal).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem h𝔞0 hv0)]
    have hm : ClassGroup.mk0 ⟨𝔞 * v.asIdeal, mul_mem h𝔞0 hv0⟩ =
        ClassGroup.mk0 ⟨𝔞, h𝔞0⟩ * ClassGroup.mk0 ⟨v.asIdeal, hv0⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    change _ * UpperTheory.V.Kum.primeCl v = 1
    rw [hvc, mul_inv_cancel]
  obtain ⟨y, hy⟩ := hprin
  have hy' : Ideal.span {y} = 𝔞 * v.asIdeal := hy.symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
    exact (mul_ne_zero h𝔞 v.ne_bot) hy'.symm
  have hXy := (xMul M K b).2.2.2.2 y hy0
  rw [hy'] at hXy
  exact ⟨_, (xMul M K b).2.1 𝔞 v.asIdeal _ _ h𝔞 v.ne_bot hXy hXv⟩
end

