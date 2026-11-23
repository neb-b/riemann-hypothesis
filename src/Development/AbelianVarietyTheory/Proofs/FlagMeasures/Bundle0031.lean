module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulRatTupEq
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.LocalWittND

theorem exists_gl {K S : Type} [Field K] [CommRing S] (s : S →+* S) (hs : ∀ x, s (s x) = x)
    (h2 : (2 : S) ≠ 0) (hS : IsField S ∨ ∃ φ : S ≃+* K × K, ∀ x, φ (s x) = (φ x).swap)
    {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (hd : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin a) S) (hX : IsUnit (Formalism.UG.cT s X * J * X).det)
    (hXY : Formalism.UG.cT s Y * J * Y = Formalism.UG.cT s X * J * X) :
    ∃ γ : GL (Fin n) S, Formalism.UG.cT s γ.1 * J * γ.1 = J ∧ γ.1 * X = Y := by
  have key : ∀ {m : ℕ} (Z : Matrix (Fin n) (Fin m) S),
      Zᵀ * Jᵀ * Z.map s = (Formalism.UG.cT s Z * J * Z)ᵀ := by
    intro m Z
    simp only [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hX' : IsUnit (Xᵀ * Jᵀ * X.map s).det := by rw [key, Matrix.det_transpose]; exact hX
  have hXY' : Yᵀ * Jᵀ * Y.map s = Xᵀ * Jᵀ * X.map s := by rw [key, key, hXY]
  have : ∃ γ : Matrix (Fin n) (Fin n) S, γᵀ * Jᵀ * γ.map s = Jᵀ ∧ γ * X = Y := by
    rcases hS with hF | ⟨φ, hφ⟩
    · letI := hF.toField
      obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero (c := s)
        h2 hs (G := Jᵀ) (fun i j => hJ i j) (X := X) (Y := Y) hX'.ne_zero hXY'
      exact ⟨γ, h1, h3⟩
    · exact GlobalTheory.HermTuple.exists_matrix_split s φ hφ Jᵀ (fun i j => hJ i j)
        (by rwa [Matrix.det_transpose]) X Y hX' hXY'
  obtain ⟨γ, h1, h3⟩ := this
  rw [key] at h1
  have h4 := Matrix.transpose_injective h1
  have hγ : IsUnit γ.det := by
    rw [← h4, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det γ).2 hγ
  exact ⟨G, by rw [hG]; exact h4, by rw [hG]; exact h3⟩

theorem gram_eq {S : Type} [CommRing S] (s : S →+* S) {n a : ℕ} (J : Matrix (Fin n) (Fin n) S)
    (Z : Fin a → Fin n → S) :
    (Matrix.of fun k l => Formalism.UG.hform s J (Z k) (Z l)) =
      Formalism.UG.cT s (Matrix.of Z)ᵀ * J * (Matrix.of Z)ᵀ := by
  ext k l
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR (F := F) R) := by
  ext k l
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, gramE, hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2

theorem invol_of_isCMExt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (∀ a, σ (σ a) = a) ∧ ∃ a, σ a ≠ a := by
  obtain ⟨-, hE, -, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨fun a => τ.injective (by rw [hσ, hσ, star_star]), ?_⟩
  by_contra hc
  push Not at hc
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ τ x
  rw [hc] at this
  exact this.symm

theorem exists_smul_eq_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K]
    {n a : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (X Y : Fin a → Fin n → K ⊗[F] E) (hX : IsUnit (gramR K σ J X).det)
    (hXY : gramR K σ J Y = gramR K σ J X) : ∃ g : HA K σ J, g • X = Y := by
  obtain ⟨hi, hne⟩ := invol_of_isCMExt hcm
  have hS := (GlobalTheory.quadBaseChange_isField_or_split F E K σ hcm.2.2.1 hi hne).1
  have hg : ∀ Z : Fin a → Fin n → K ⊗[F] E, gramR K σ J Z = _ :=
    fun Z => gram_eq (sigR K σ) (JR K J) Z
  have h2 : (2 : K ⊗[F] E) ≠ 0 := by
    have : inclR (F := F) K (2 : E) ≠ 0 := by
      rw [map_ne_zero]; exact two_ne_zero
    rwa [map_ofNat] at this
  obtain ⟨γ, h1, h3⟩ := exists_gl (sigR K σ)
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k e => exact congrArg (k ⊗ₜ[F] ·) (hi e)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    h2 hS (JR K J)
    (fun i j => by
      show (1 : K) ⊗ₜ[F] σ (J j i) = (1 : K) ⊗ₜ[F] J i j
      rw [hJ.1])
    (by
      have := (hJ.2.isUnit).map (inclR (F := F) K)
      rwa [RingHom.map_det] at this)
    (Matrix.of X)ᵀ (Matrix.of Y)ᵀ (by rw [← hg]; exact hX) (by rw [← hg, ← hg]; exact hXY)
  refine ⟨(⟨γ, h1⟩ : HR K σ J), ?_⟩
  funext k i
  exact congrFun (congrFun h3 i) k

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (X0 : Fin a → Fin n → E), (gramE σ J X0).det ≠ 0 → ∀ y : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J y = (gramE σ J X0).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v a X0 hX y hy
  refine exists_smul_eq_field hcm (Fv F v) hJ _ _ ?_ (by rw [hy, gramR_ratTup])
  have := hX.isUnit.map (inclR (F := F) (Fv F v))
  rw [gramR_ratTup]
  rwa [RingHom.map_det] at this

end GlobalTheory.LocalWittND
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceChar
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceChar

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem psi0_eq_one_of_conj_eq_neg {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {z : E} (hz : L.cj z = -z) : L.psi0 z = 1 := by
  set w := algebraMap F E (1 / 2) * z with hw
  have hcw : L.cj w = -w := by
    rw [hw, map_mul, AlgEquiv.commutes, hz, mul_neg]
  have hzw : z = w + w := by
    rw [hw, ← add_mul, ← map_add (f := _)]
    norm_num
  have h1 : L.psi0 w = L.psi0 (-w) := by rw [← hcw, _root_.Formalism.MainNotions.S.Loc.LocE.local_additive_char_conj]
  rw [hzw, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h1]
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem ker_mkQ_comp_mulLeft_pow_eq_span' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n k : ℕ) :
    ((Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))).ker =
      Ideal.span {ϖ ^ n} := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  rw [pow_add, mul_comm (ϖ ^ n), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_succ_eq_resQ_mul {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ (n + 1)}) =
      _root_.GlobalTheory.HL.resQ ϖ * Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) := by
  rw [add_comm n 1]
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ n))
  have hS : Nat.card (LinearMap.range f) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    have hk := ker_mkQ_comp_mulLeft_pow_eq_span' hϖ 1 n
    rw [pow_one] at hk
    rw [← hk]
    exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
  set g := (Submodule.mkQ (LinearMap.range f)).comp (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)}))
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : g.ker = Ideal.span {ϖ ^ n} := by
    ext y
    simp only [g, f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      rw [Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
      have h2 : ϖ ^ n ∣ ϖ ^ (1 + n) := pow_dvd_pow _ (by omega)
      have h4 : ϖ ^ n ∣ ϖ ^ n * z := dvd_mul_right _ _
      simpa using (dvd_sub h4 (h2.trans hz))
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have e := (g.quotKerEquivOfSurjective hg).toEquiv
  rw [hker] at e
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f), hS, Nat.card_congr e]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) = _root_.GlobalTheory.HL.resQ ϖ ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ n ih => rw [card_quotient_span_pow_succ_eq_resQ_mul hϖ, ih, pow_succ, mul_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem resQ_pos' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [← h]
  exact Nat.card_pos (α := 𝓀[F])

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_quotient_span_pow_flag_measures {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) :=
  Nat.finite_of_card_ne_zero (by rw [card_quotient_span_pow_eq_resQ_pow hϖ]; exact pow_ne_zero _ (resQ_pos' hϖ).ne')

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_nat_mul_mem_integer (x : F) : ∃ N : ℕ, 0 < N ∧ (N : F) * x ∈ 𝒪[F] := by
  by_cases hx : x ∈ 𝒪[F]
  · exact ⟨1, one_pos, by simpa using hx⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hinv : x⁻¹ ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
  set b : 𝒪[F] := ⟨x⁻¹, hinv⟩ with hbdef
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : F) = 0 := by rw [h]; rfl
    exact inv_ne_zero hx0 this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨n, u, hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}), ?_, ?_⟩
  · haveI := finite_quotient_span_pow_flag_measures hϖ n
    exact Nat.card_pos
  have hmem : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : 𝒪[F]) ∈ Ideal.span {ϖ ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
    exact card_nsmul_eq_zero'
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
  have hxb : x * (b : F) = 1 := mul_inv_cancel₀ hx0
  rw [hb] at hxb
  have hu : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) = 1 := Units.inv_mul u
  have hu' : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
    rw [← Subring.coe_mul, hu]; rfl
  have hN : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : F) = ((w : 𝒪[F]) : F) * ((ϖ : 𝒪[F]) : F) ^ n := by
    rw [← map_natCast (𝒪[F]).subtype, ← hw]; push_cast; rfl
  have : (Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : F) * x = ((w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : 𝒪[F]) : F) := by
    rw [hN]
    push_cast at hxb ⊢
    linear_combination ((w : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * hxb - ((w : F) * ((ϖ : 𝒪[F]) : F) ^ n * x) * hu'
  rw [this]
  exact (w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])).2


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.TraceChar.exists_trace_char : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∃ ψ : AddChar F ℂ, (∀ x : F, ‖ψ x‖ = 1) ∧ (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) ∧ ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
  intro F _ _ _ _ _ E _ _ _ L
  let ψ : AddChar F ℂ := L.psi0.compAddMonoidHom
    ((algebraMap F E).toAddMonoidHom.comp (AddMonoidHom.mulLeft (1 / 2 : F)))
  have hψ : ∀ c, ψ c = L.psi0 (algebraMap F E (1 / 2 * c)) := fun c => rfl
  have hcomp : ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
    intro y c h
    have hz : L.cj (y - algebraMap F E (1 / 2 * c)) = -(y - algebraMap F E (1 / 2 * c)) := by
      rw [map_sub, AlgEquiv.commutes]
      have : L.cj y = algebraMap F E c - y := by rw [← h]; ring
      rw [this]
      have : algebraMap F E c = algebraMap F E (1 / 2 * c) + algebraMap F E (1 / 2 * c) := by
        rw [← map_add (f := _)]; congr 1; ring
      rw [this]; ring
    have := psi0_eq_one_of_conj_eq_neg L hz
    rw [hψ, ← one_mul (L.psi0 (algebraMap F E _)), ← this, ← AddChar.map_add_eq_mul, sub_add_cancel]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hint : ∀ c : 𝒪[F], ψ c = 1 := by
    intro c
    obtain ⟨e, he, htr⟩ := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).1 c
    rw [← hcomp e c htr, ← one_mul e]
    exact (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L 1).2 (one_mem _) e he
  refine ⟨ψ, ?_, ?_, hcomp⟩
  · intro x
    obtain ⟨N, hN, hNx⟩ := exists_nat_mul_mem_integer x
    have h1 : ψ x ^ N = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
      exact hint ⟨_, hNx⟩
    have h2 : ‖ψ x‖ ^ N = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2
  · intro x
    constructor
    · intro hx
      rw [← _root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L]
      refine (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L _).1 fun e he => ?_
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L he
      have htr : algebraMap F E x * e + L.cj (algebraMap F E x * e) = algebraMap F E (x * c) := by
        rw [map_mul, AlgEquiv.commutes, ← mul_add, hc, map_mul]
      rw [hcomp _ _ htr]
      exact hx c
    · intro hx y
      exact hint ⟨x * y, mul_mem hx y.2⟩

end GlobalTheory.TraceChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameUnipotentUnitriangular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameTri

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x a : Fin n → E) :
    hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (c : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * hf L Hm (g i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem coeff_of_mem (g : Fin (r + 1) → S.V) {j : ℕ} {v : S.V} (hv : v ∈ S.spanTo g j) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), j ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun a ha => ?_, ?_⟩
    · have hi' : (i : ℕ) < j := hi
      have : a ≠ i := by rintro rfl; omega
      simp [this]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨a • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

section
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include hg hd in
theorem linInd : LinearIndependent E g := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have key : ∀ y, ∑ a, c a * hf L S.Hm (g a) y = 0 := by
    intro y
    rw [← hf_sum_left, hc]; simp [hf]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := key (g (Fin.last r))
    simp only [hg, and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have hu : IsUnit (-algebraMap F E t) := (t.isUnit.map (algebraMap F E)).neg
    exact (hu.mul_left_eq_zero).1 h
  · have h := key (gs j)
    simpa [hd] using h

include hg in
theorem last_mem_perp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := hi
    have : i ≠ Fin.last r := by rintro rfl; simp at hi'
    simp [hg, this]
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [hf_smul_right, hx, mul_zero]

include hg in
theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) :
    n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨_, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h3.2 _ (last_mem_perp S g t hg)
  · have h := (Subgroup.mem_iInf.1 h2 j).2 (g j.castSucc) (mem_spanTo S g (by simp))
    exact h

include hg in
theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {v : S.V} (hv : v ∈ S.spanTo g j) :
    n v ∈ S.spanTo g j := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < j := hi
    have h := Submodule.add_mem _ (spanTo_mono S g hi'.le (sub_mem S g t hg hn i)) (mem_spanTo S g hi')
    simpa using h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

include hg in
theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (v : S.V) :
    n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem S g t hg hn j⟩
  have h' := map_mem S g t hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n v) = v := n.symm_apply_apply v
  rwa [e] at h'

include hg in
theorem spanTo_comp {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) :
    S.spanTo (fun b => n (g b)) j = S.spanTo g j := by
  have h : S.spanTo (fun b => n (g b)) j = (S.spanTo g j).map (n : S.V →ₗ[E] S.V) := by
    unfold Frames.spanTo
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [h]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem S g t hg hn j hx
  · intro hv
    refine ⟨n.symm v, ?_, by simp⟩
    apply (map_mem_iff S g t hg hn j _).1
    simpa using hv

include hg in
theorem exists_tri {n : S.GLV} (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  choose c hc hc' using fun j => coeff_of_mem S g (sub_mem S g t hg hn j)
  refine ⟨Matrix.of fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i (le_of_lt hij), hij.ne']
  · simp [hc i i le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← hc' j, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp

end

end GlobalTheory.HL.FrameTri

namespace GlobalTheory.HL

theorem frame_unipotent_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → LinearIndependent E g ∧ ∀ n ∈ S.Nof g, (∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (g j) = ∑ i, s i j • g i) ∧ (∀ j, S.spanTo (fun b => n (g b)) j = S.spanTo g j) ∧ (∀ j, ∀ v, n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j) ∧ ∀ v, n v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs h
  obtain ⟨t, hg, hd⟩ : ∃ t : Fˣ, (∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0) ∧
      ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S.T, S.gram, S.dual⟩
    · exact ⟨S.T', S.gram', S.dual'⟩
  exact ⟨FrameTri.linInd S g gs t hg hd, fun n hn => ⟨FrameTri.exists_tri S g t hg hn,
    FrameTri.spanTo_comp S g t hg hn, FrameTri.map_mem_iff S g t hg hn, hn.2.1⟩⟩

end GlobalTheory.HL
end

