module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
section
noncomputable section

namespace PIW.ClassFinD

open NumberField IsDedekindDomain

def IsUpperUni {R : Type} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def IsDiagM {R : Type} [CommRing R] {n : ℕ} (t : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, i ≠ j → t i j = 0

def IwasawaAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    ∃ u t k : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ k ∈ KGL F n ∧ g = u * t * k

def UnipApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (u t : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    IsUpperUni u.val → IsDiagM t.val →
      ∃ ν : GL (Fin n) F, ∃ w ∈ KGL F n, u = glIncl F n ν * t * w * t⁻¹

def IdeleClassFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ C : Finset (FiniteAdeleRing (𝓞 F) F)ˣ, ∀ a : (FiniteAdeleRing (𝓞 F) F)ˣ,
      ∃ f : Fˣ, ∃ c ∈ C, ∃ e : (FiniteAdeleRing (𝓞 F) F)ˣ,
        (e : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        ((e⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        a = Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) f * c * e

def diagGL {R : Type} [CommRing R] (n : ℕ) : (Fin n → Rˣ) →* GL (Fin n) R :=
  (Units.map (Matrix.diagonalRingHom (Fin n) R : (Fin n → R) →* Matrix (Fin n) (Fin n) R)).comp
    (MulEquiv.piUnits.symm : (Fin n → Rˣ) ≃* (Fin n → R)ˣ).toMonoidHom

theorem diagGL_val {R : Type} [CommRing R] (n : ℕ) (τ : Fin n → Rˣ) :
    (diagGL n τ).val = Matrix.diagonal fun i => (τ i : R) := rfl

theorem glIncl_diagGL (F : Type) [Field F] [NumberField F] (n : ℕ) (f : Fin n → Fˣ) :
    glIncl F n (diagGL n f) =
      diagGL n (fun i => Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (f i)) := by
  apply Units.ext
  ext i j
  simp [diagGL_val, Matrix.diagonal_apply, glIncl, apply_ite]

theorem diag_eq_diagGL {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : IsDiagM t.val) :
    ∃ τ : Fin n → Rˣ, t = diagGL n τ := by
  have hunit : ∀ i, IsUnit (t.val i i) := by
    intro i
    have h : (t⁻¹.val * t.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single i (fun k _ hki => by rw [ht k i hki, mul_zero]) (by simp)] at h
    exact ⟨⟨t.val i i, t⁻¹.val i i, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨fun i => (hunit i).unit, Units.ext ?_⟩
  rw [diagGL_val]
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    exact (IsUnit.unit_spec _).symm
  · exact ht i j hij

theorem diagGL_mem_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) (e : Fin n → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (h1 : ∀ i, (e i : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F)
    (h2 : ∀ i, ((e i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ).val ∈ Ohat F) : diagGL n e ∈ KGL F n := by
  have hd : ∀ d : Fin n → FiniteAdeleRing (𝓞 F) F, (∀ i, d i ∈ Ohat F) →
      MatInt (Matrix.diagonal d) := by
    intro d hd i j
    rw [Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hd i
    · exact (Ohat F).zero_mem
  show MatInt (diagGL n e).val ∧ MatInt (diagGL n e)⁻¹.val
  constructor
  · rw [diagGL_val]
    exact hd _ h1
  · rw [← map_inv (diagGL (R := FiniteAdeleRing (𝓞 F) F) n), diagGL_val]
    exact hd _ fun i => h2 i

theorem borelKGL_of (hI : IwasawaAf) (hU : UnipApprox) (hC : IdeleClassFin) : BorelKGL := by
  classical
  intro F _ _ n
  obtain ⟨C, hCa⟩ := hC F
  refine ⟨(Fintype.piFinset fun _ : Fin n => C).image (diagGL n), fun x => ?_⟩
  obtain ⟨u, t, k, hu, ht, hk, rfl⟩ := hI F n x
  obtain ⟨ν, w, hw, huν⟩ := hU F n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose f c hc e he1 he2 hτ using fun i => hCa (τ i)
  have hsplit : diagGL n τ = glIncl F n (diagGL n f) * diagGL n c * diagGL n e := by
    rw [glIncl_diagGL, ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n),
      ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n)]
    congr 1
    funext i
    exact hτ i
  refine ⟨ν * diagGL n f, diagGL n c, Finset.mem_image.mpr ⟨c, Fintype.mem_piFinset.mpr hc, rfl⟩,
    diagGL n e * (w * k),
    (KGL F n).mul_mem (diagGL_mem_KGL F n e he1 he2) ((KGL F n).mul_mem hw hk), ?_⟩
  rw [huν, map_mul, hsplit]
  group

end PIW.ClassFinD

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.ExistsNeZeroMem
section
noncomputable section

namespace PIW.ClassFinD.Icf

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

theorem v_mul (x y : FiniteAdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((x * y) w) = Valued.v (x w) * Valued.v (y w) := by
  have : (x * y) w = x w * y w := rfl
  rw [this, map_mul]

theorem v_algR (r : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) w) = w.intValuation r :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w r

theorem v_algF (f : F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) f) w) = w.valuation F f :=
  valuedAdicCompletion_eq_valuation' w f

theorem v_unit_mul_inv (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) * Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) w) = 1 := by
  rw [← v_mul, Units.mul_inv]
  have : (1 : FiniteAdeleRing (𝓞 F) F) w = 1 := rfl
  rw [this, map_one]

theorem v_unit_ne (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := by
  intro h
  have := v_unit_mul_inv b w
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem v_inv (b : (FiniteAdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w) =
      (Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w))⁻¹ :=
  (eq_inv_of_mul_eq_one_right (v_unit_mul_inv b w))

def latI (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : Ideal (𝓞 F) where
  carrier := {x | ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w)}
  add_mem' := fun {x y} hx hy w => (Valuation.map_add _ x y).trans (max_le (hx w) (hy w))
  zero_mem' := fun w => by rw [map_zero]; exact zero_le
  smul_mem' := fun c x hx w => by
    rw [smul_eq_mul, map_mul]
    exact (mul_le_of_le_one_left' (w.intValuation_le_one c)).trans (hx w)

theorem exists_ne_zero_mem (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : ∃ r : 𝓞 F, r ≠ 0 ∧ r ∈ latI b := by
  obtain ⟨r, hr, h⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den
    (((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  refine ⟨r, hr, fun w => ?_⟩
  have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r *
      ((b⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1 := h w
  rw [v_mul, v_algR, v_inv] at h1
  have hpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) := zero_lt_iff.2 (v_unit_ne b w)
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact h1

theorem approx (b : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ∈ latI b ∧ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤ v.intValuation a := by
  obtain ⟨r0, hr0, hr0I⟩ := exists_ne_zero_mem b
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hr : r0 * π ≠ 0 := mul_ne_zero hr0 hπ0
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (b : FiniteAdeleRing (𝓞 F) F)
    (fun w => hb w) (r0 * π) hr
  have hA : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) = w.intValuation a :=
    fun w => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R w a
  have hsmall : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation (r0 * π) ≤ w.intValuation r0 := by
    intro w
    rw [map_mul]
    exact mul_le_of_le_one_right' (w.intValuation_le_one π)
  refine ⟨a, fun w => ?_, ?_⟩
  · rw [← hA w]
    have e : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) =
        (b : FiniteAdeleRing (𝓞 F) F) w -
          ((b : FiniteAdeleRing (𝓞 F) F) w - algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le le_rfl ?_)
    exact (ha w).trans ((hsmall w).trans (hr0I w))
  · by_contra hlt
    rw [not_le] at hlt
    have hbpos : 0 < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := zero_lt_iff.2 (v_unit_ne b v)
    have hπlt : v.intValuation π < 1 := (v.intValuation_lt_one_iff_mem π).2 hπv
    have h2 : Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) := by
      calc _ ≤ v.intValuation (r0 * π) := ha v
        _ = v.intValuation r0 * v.intValuation π := map_mul _ _ _
        _ ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * v.intValuation π := by
          gcongr
          exact hr0I v
        _ < Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) * 1 := by
          exact mul_lt_mul_of_pos_left hπlt hbpos
        _ = _ := mul_one _
    have e : (b : FiniteAdeleRing (𝓞 F) F) v = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) +
        ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
      ring
    have h3 := Valuation.map_add (Valued.v : Valuation (v.adicCompletion F) _)
      (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      ((b : FiniteAdeleRing (𝓞 F) F) v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
    rw [← e, hA v] at h3
    exact absurd h3 (not_le.2 (max_lt hlt h2))

theorem val_le_of_le (b b' : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1)
    {x y : 𝓞 F} (h : Ideal.span {x} * latI b ≤ Ideal.span {y} * latI b') (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) ≤
      v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
  obtain ⟨a, haI, hav⟩ := approx b hb v
  obtain ⟨z, hzI, hz⟩ := (Ideal.span_singleton_mul_le_span_singleton_mul.1 h) a haI
  calc v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v)
      ≤ v.intValuation x * v.intValuation a := by gcongr
    _ = v.intValuation (x * a) := (map_mul _ _ _).symm
    _ = v.intValuation (y * z) := by rw [hz]
    _ = v.intValuation y * v.intValuation z := map_mul _ _ _
    _ ≤ v.intValuation y * Valued.v ((b' : FiniteAdeleRing (𝓞 F) F) v) := by
      gcongr
      exact hzI v

end PIW.ClassFinD.Icf

end
end

