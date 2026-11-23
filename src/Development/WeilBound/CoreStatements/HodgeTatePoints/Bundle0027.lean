module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHostA
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHost
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

namespace Biq

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (B : Biq F m)

def W : 𝓞 F := ⟨B.w, B.integral_w⟩

def J : 𝓞 F := ⟨B.i, B.integral_i⟩

def mk4 (v : ℤ × ℤ × ℤ × ℤ) : 𝓞 F := v.1 + v.2.1 * B.W + v.2.2.1 * B.J + v.2.2.2 * (B.W * B.J)

theorem coe_W : algebraMap (𝓞 F) F B.W = B.w := rfl
theorem coe_J : algebraMap (𝓞 F) F B.J = B.i := rfl

theorem W_sq : B.W * B.W = B.W - m := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_natCast, coe_W] using B.w_sq)

theorem J_sq : B.J * B.J = -1 := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one, coe_J] using B.i_sq)

theorem coe_mk_quad (v : ℤ × ℤ × ℤ × ℤ) : algebraMap (𝓞 F) F (B.mk4 v) =
    v.1 + v.2.1 * B.w + v.2.2.1 * B.i + v.2.2.2 * (B.w * B.i) := by
  simp only [mk4, map_add (f := _), map_mul, map_intCast, coe_W, coe_J]

theorem mk_quad_injective : Function.Injective B.mk4 := fun v v' h => by
  have h' := congrArg (algebraMap (𝓞 F) F) h
  rw [coe_mk_quad, coe_mk_quad] at h'
  obtain ⟨h1, h2, h3, h4⟩ := B.indep (v.1 - v'.1) (v.2.1 - v'.2.1) (v.2.2.1 - v'.2.2.1) (v.2.2.2 - v'.2.2.2) (by
    push_cast; linear_combination h')
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact_mod_cast sub_eq_zero.1 h1
  · exact_mod_cast sub_eq_zero.1 h2
  · exact_mod_cast sub_eq_zero.1 h3
  · exact_mod_cast sub_eq_zero.1 h4

theorem mk_quad_surjective {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) : Function.Surjective B.mk4 := fun x => by
  obtain ⟨a, b, c, e, h⟩ := B.coords hd hp x.isIntegral_coe
  exact ⟨(a, b, c, e), RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, coe_mk_quad]; exact h.symm)⟩

theorem σ_σ (x : F) : B.σ (B.σ x) = x := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add (f := _), map_mul, map_ratCast, B.σw, B.σi, map_neg, neg_neg]

def σO : 𝓞 F ≃+* 𝓞 F :=
  RingOfIntegers.mapRingEquiv (RingEquiv.ofRingHom B.σ B.σ (RingHom.ext B.σ_σ) (RingHom.ext B.σ_σ))

theorem sigma_W : B.σO B.W = B.W := RingOfIntegers.ext B.σw

theorem σO_J : B.σO B.J = -B.J := RingOfIntegers.ext B.σi

variable [IsCMField F]

theorem complexConj_eq (hm : 0 < m) (x : F) : IsCMField.complexConj F x = B.σ (B.τ x) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, B.conj_eq hm]

include B in
theorem unramified {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) :
    Algebra.Unramified (𝓞 (maximalRealSubfield F)) (𝓞 F) := by
  have hm : 0 < m := by omega
  let R := 𝓞 (maximalRealSubfield F)
  let δ := KaehlerDifferential.D R (𝓞 F)
  have h1 : (2 * B.J) • δ B.J = 0 := by
    have := congrArg δ B.J_sq
    rw [Derivation.leibniz, map_neg, Derivation.map_one_eq_zero, neg_zero] at this
    rw [two_mul, add_smul, this]
  have h2 : (2 * B.W - 1) • δ B.W = 0 := by
    have := congrArg δ B.W_sq
    rw [Derivation.leibniz, map_sub, Derivation.map_natCast, sub_zero] at this
    rw [two_mul, sub_smul, add_smul, this, one_smul, sub_self]
  have h3 : δ (B.J * (B.W + B.W - 1)) = 0 := by
    obtain ⟨r, hr⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff F (B.J * (B.W + B.W - 1))).1
      (RingOfIntegers.ext (by
        rw [IsCMField.coe_ringOfIntegersComplexConj, B.complexConj_eq hm]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_add (f := _), map_one, coe_W, coe_J, B.τi, B.τw,
          B.σi, B.σw]
        ring))
    rw [← hr, Derivation.map_algebraMap]
  rw [Derivation.leibniz, map_sub, map_add (f := _), Derivation.map_one_eq_zero, sub_zero] at h3
  have hJ : δ B.J = 0 := by
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (2 * B.J) + (2 * B.W - 1) * (B.W + B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    have e2 : (2 * B.W - 1) • ((B.W + B.W - 1) • δ B.J) = 0 := by
      rw [eq_neg_of_add_eq_zero_right h3, smul_neg, smul_comm, smul_add, h2, add_zero, smul_zero, neg_zero]
    rw [← one_smul (𝓞 F) (δ B.J), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h1, e2, smul_zero, add_zero]
  have hW : δ B.W = 0 := by
    rw [hJ, smul_zero, add_zero, ← two_smul (𝓞 F), smul_smul] at h3
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (B.J * 2) + (2 * B.W - 1) * (2 * B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    rw [← one_smul (𝓞 F) (δ B.W), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h3, h2, smul_zero, smul_zero, add_zero]
  have hall : ∀ x, δ x = 0 := fun x => by
    obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd hp x
    simp only [mk4, map_add (f := _), Derivation.leibniz, hW, hJ, Derivation.map_intCast, smul_zero, add_zero]
  have hs : Subsingleton (Ω[𝓞 F⁄R]) := by
    rw [← Submodule.subsingleton_iff (𝓞 F), ← subsingleton_iff_bot_eq_top, eq_comm,
      ← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  have : Algebra.FormallyUnramified R (𝓞 F) := ⟨hs⟩
  have : Algebra.FiniteType R (𝓞 F) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R (𝓞 F)
  exact {}

end Biq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mat (w : 𝓞 E) (v : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (𝓞 E) :=
  !![v.1 + v.2.1 * w, -(v.2.2.1 + v.2.2.2 * w); v.2.2.1 + v.2.2.2 * w, v.1 + v.2.1 * w]


set_option maxHeartbeats 1600000 in
theorem exists_pairHost {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (H' : Host E'), Nonempty (PairHost H H') := by
  obtain ⟨m, hd⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hm : 0 < m := by omega
  obtain ⟨F, _, _, ⟨B⟩⟩ := exists_biq m (by rw [show 4 * m - 1 = H.d by omega]; exact H.d_prime)
  have := B.numberField
  have := B.isCMField hm
  have hdO : (H.d : 𝓞 F) + 1 = 4 * m := by exact_mod_cast hd
  let H' : Host F :=
    { d := H.d, d_mod := H.d_mod, d_prime := H.d_prime, rt := 2 * B.W - 1
      rt_sq := by linear_combination 4 * B.W_sq + hdO
      w0 := B.W, two_weight_eq_one_add_root := by ring
      bar := (IsCMField.ringOfIntegersComplexConj F).toRingEquiv
      bar_eq := fun _ => rfl
      unram := B.unramified hd H.d_prime
      rt0 := H.rt0, sqrt_neg_disc_sq := H.sqrt_neg_disc_sq }
  have hbW : H'.bar B.W = 1 - B.W := GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator H'
  have hbJ : H'.bar B.J = -B.J := RingOfIntegers.ext (by
    rw [H'.bar_eq, B.complexConj_eq hm]
    show B.σ (B.τ B.i) = -B.i
    rw [B.τi, B.σi])
  have hw : H.w0 * H.w0 = H.w0 - m := by
    have hdE : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hd
    have h1 := H.rt_sq
    rw [GlobalTheory.HostModel.rt_eq] at h1
    have : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - m)) = 0 := by linear_combination h1 - hdE
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by norm_num))
  let e := Equiv.ofBijective B.mk4 ⟨B.mk_quad_injective, B.mk_quad_surjective hd H.d_prime⟩
  have he : ∀ (x : 𝓞 F) v, x = B.mk4 v → mat H.w0 (e.symm x) = mat H.w0 v := by
    rintro _ v rfl
    rw [show e.symm (B.mk4 v) = v from e.symm_apply_apply v]
  let ψ : 𝓞 F →+* Matrix (Fin 2) (Fin 2) (𝓞 E) :=
    { toFun := fun x => mat H.w0 (e.symm x)
      map_one' := by
        rw [he 1 (1, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_zero' := by
        rw [he 0 (0, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_add' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a + a', b + b', c + c', f + f') (by simp only [Biq.mk4]; push_cast; ring)]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
      map_mul' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a * a' - m * b * b' - c * c' + m * f * f',
          a * b' + b * a' + b * b' - c * f' - f * c' - f * f', a * c' + c * a' - m * b * f' - m * f * b',
          a * f' + b * c' + b * f' + c * b' + f * a' + f * b') (by
            simp only [Biq.mk4]; push_cast
            linear_combination ((b * b' + (b * f' + f * b') * B.J - f * f' : 𝓞 F)) * B.W_sq +
              ((c + f * B.W) * (c' + f' * B.W) : 𝓞 F) * B.J_sq)]
        ext1 i j
        fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw
        · linear_combination (b * f' + f * b' : 𝓞 E) * hw
        · linear_combination (-(b * f' + f * b') : 𝓞 E) * hw
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw }
  have hψ : ∀ (x : 𝓞 F) v, x = B.mk4 v → ψ x = mat H.w0 v := he
  clear_value ψ
  refine ⟨F, inferInstance, inferInstance, inferInstance, H', ⟨⟨ψ, B.σO, fun x i j => ?_, ?_, fun x => ?_, ?_,
    fun k _ _ τ τ' h => ?_⟩⟩⟩
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a + b, -b, -c - f, f) (by
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hbW, hbJ]; push_cast; ring)]
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  · rw [hψ _ (0, 1, 0, 0) (by simp [Biq.mk4, H'])]
    ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a, b, -c, -f) (by
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, B.sigma_W, B.σO_J]; push_cast; ring)]
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  · show B.σO (2 * B.W - 1) = 2 * B.W - 1
    rw [map_sub, map_mul, map_ofNat, map_one, B.sigma_W]
  · have hW : τ' B.W = τ B.W := by
      change τ (2 * B.W - 1) = τ' (2 * B.W - 1) at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination (-1 / 2 : k) * h
    have h1 := congrArg τ B.J_sq
    have h2 := congrArg τ' B.J_sq
    simp only [map_mul, map_neg, map_one] at h1 h2
    have : (τ' B.J - τ B.J) * (τ' B.J + τ B.J) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h3 | h3
    · refine Or.inl (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hW, sub_eq_zero.1 h3]
    · refine Or.inr (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      show _ = τ (B.σO _)
      simp only [Biq.mk4, map_add (f := _), map_mul, map_intCast, hW, eq_neg_of_add_eq_zero_left h3, B.sigma_W, B.σO_J, map_neg]

end PositivityTheory.HtPt.Kftwo
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinIso
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

theorem chRing_mem {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {ι : Type} {J : ι → Ω} {d : ι}
    {S : Subring Ω} (ho : ∀ r : o, algebraMap o Ω r ∈ S) (h : ∀ q, J q / J d ∈ S) :
    ∀ a ∈ chRing o J d, a ∈ S := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact h q
  | algebraMap r => exact ho r
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem eq_of_units {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} {p q : Cpt M.ξ} (hp : InChart M.ξ x c p) (hq : InChart M.ξ x c q)
    (h : ∀ u ∈ chRing o x c, unitAt M.ξ p u ↔ unitAt M.ξ q u) : p = q := by
  have hle : ∀ {p q : Cpt M.ξ}, InChart M.ξ x c p → InChart M.ξ x c q →
      (∀ u ∈ chRing o x c, unitAt M.ξ p u → unitAt M.ξ q u) → regAt M.ξ p ≤ regAt M.ξ q := by
    intro p q hp hq h a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp).2 a).1 ha
    exact ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).2 _).2 ⟨u, hu, v, hv, h v hv hvu, rfl⟩
  have h1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p q).1 (hle hp hq fun u hu => (h u hu).1)
  have h2 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M q p).1 (hle hq hp fun u hu => (h u hu).2)
  exact Subtype.ext (h2.antisymm h1).eq

theorem isoAt_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M κ' _ w M' f hd p ⟨l, hl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hJ0 : joinCo (RingHom.id Ω) x w (c, l) ≠ 0 := mul_ne_zero hc.1 hl.1
  have ratio : ∀ j m, joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
      (x j / x c) * (w m / w l) := fun j m => by
    simp only [joinCo, RingHom.id_apply, mul_div_mul_comm]
  have hpJ : ∀ q, joinCo (RingHom.id Ω) x w q / joinCo (RingHom.id Ω) x w (c, l) ∈ regAt M.ξ p := by
    rintro ⟨j, m⟩
    rw [ratio]
    exact mul_mem (hc.2 j) (hl.2 m)
  have hAp := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).1
  have hctr : p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ :=
    ⟨(c, l), hJ0, chRing_mem (fun r => hAp _ (Subalgebra.algebraMap_mem _ r)) hpJ⟩
  obtain ⟨p', ⟨hle', hun'⟩, -, hch'⟩ :=
    PositivityTheory.HtPt.Mb.centre o Ω (κ × κ') (joinCo (RingHom.id Ω) x w) M' M.X Ω M.ξ (RingHom.id Ω) p hctr
  have hle : ∀ a ∈ regAt M'.ξ p', a ∈ regAt M.ξ p := hle'
  have hun : ∀ a ∈ regAt M'.ξ p', unitAt M.ξ p a → unitAt M'.ξ p' a := hun'
  have hp'c : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p' := hch' (c, l) hJ0 hpJ
  have dom := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω M'.ξ (RingHom.id Ω) f hd
  obtain ⟨h, hq1', hq2'⟩ := dom p'
  have hq1 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, a ∈ regAt M'.ξ p' := hq1'
  have hq2 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, unitAt M'.ξ p' a → unitAt M.ξ ⟨f p'.1, h⟩ a := hq2'
  have hx : ∀ j, x j / x c ∈ regAt M'.ξ p' := fun j => by
    have e : joinCo (RingHom.id Ω) x w (j, l) / joinCo (RingHom.id Ω) x w (c, l) = x j / x c := by
      rw [ratio, div_self hl.1, mul_one]
    rw [← e]
    exact hp'c.2 (j, l)
  obtain ⟨c₁, hc₁⟩ := M.tie.cover ⟨f p'.1, h⟩
  have hu : unitAt M.ξ ⟨f p'.1, h⟩ (x c / x c₁) :=
    hq2 _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, hq1 _ (hc₁.2 c), by rw [inv_div]; exact hx c₁⟩
  have hqc : InChart M.ξ x c ⟨f p'.1, h⟩ := ⟨hc.1, fun j => by
    have e : x j / x c = (x j / x c₁) * (x c / x c₁)⁻¹ := by
      have h1 := hc.1
      have h2 := hc₁.1
      field_simp
    rw [e]
    exact mul_mem (hc₁.2 j) hu.2.2⟩
  have hqp : (⟨f p'.1, h⟩ : Cpt M.ξ) = p := by
    refine eq_of_units M hqc hc fun u hu => ?_
    have uq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hqc).1 u hu
    exact ⟨fun k => ⟨k.1, hAp u hu, hle _ (hq1 _ k.2.2)⟩, fun k => hq2 u uq (hun u (hq1 u uq) k)⟩
  have e' : f p'.1 = p.1 := congrArg Subtype.val hqp
  rw [hqp] at hq1
  have hreg : regAt M'.ξ p' = regAt M.ξ p := le_antisymm hle hq1
  have uniq : ∀ p'' : Cpt M'.ξ, f p''.1 = p.1 → p'' = p' := by
    intro p'' e
    obtain ⟨h2, r1', r2'⟩ := dom p''
    have e2 : (⟨f p''.1, h2⟩ : Cpt M.ξ) = p := Subtype.ext e
    rw [e2] at r1' r2'
    have r1 : ∀ a ∈ regAt M.ξ p, a ∈ regAt M'.ξ p'' := r1'
    have r2 : ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p'' a → unitAt M.ξ p a := r2'
    have hch : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p'' := ⟨hJ0, fun q => r1 _ (hpJ q)⟩
    refine eq_of_units M' hch hp'c fun u hu => ?_
    have up' := (PositivityTheory.HtPt.Ma.regat_loc o Ω (κ × κ') _ M' (c, l) p' hp'c).1 u hu
    have up := hle u up'
    exact ⟨fun k => hun u up' (r2 u up k), fun k => ⟨k.1, r1 u up, r1 _ (hle _ k.2.2)⟩⟩
  refine ⟨⟨p', e', fun p'' e => uniq p'' e⟩, fun p'' e => ?_, hd⟩
  rw [uniq p'' e, hreg, Subring.map_id]

end PositivityTheory.HtPt.Mb.LJoinIso.JoinIso


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_iso : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinIso.JoinIso.isoAt_of_chart
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhQuot
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem quot : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsFinite Γ₁.G.hom → IsFinite Γ.G.hom → Flat a.left → Surjective a.left → quotOrder α (Γ₁.btOrder ⊤) = Γ.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hpt hfin₁ hfin hfl hsurj
  haveI : IsAffine Γ.G.left := isAffine_of_isAffineHom Γ.G.hom
  haveI : IsAffine Γ₁.G.left := isAffine_of_isAffineHom Γ₁.G.hom
  have hα : Function.Surjective α := by
    intro t
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    obtain ⟨y, hy⟩ := a.left.surjective ((Γ.pt t).left z)
    have hgen : (Γ₁.G.hom y).asIdeal = ⊥ := by
      have e1 : Γ₁.G.hom y = Γ.G.hom ((Γ.pt t).left z) := by
        rw [← hy, ← Scheme.Hom.comp_apply, Over.w a]
      rw [e1, ← Scheme.Hom.comp_apply, Over.w (Γ.pt t)]
      show (PrimeSpectrum.comap (algebraMap R (FractionRing R)) z).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal]
      have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
      rw [hz]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    obtain ⟨h, x, hx⟩ := Γ₁.pt_onto y hgen
    refine ⟨h, Γ.pt_inj (α h) t x z ?_⟩
    have e2 : a.left ((Γ₁.pt h).left x) = (Γ.pt (α h)).left x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hpt h]
    rw [← e2, hx, hy]
  have valAt_top : ∀ {B : Type} [CommRing B] {X : Scheme.{0}}
      (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)),
      valAt x ⊤ h s = val x s := by
    intro B _ X x h s
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have sec_ext : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)}, (∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') → s = s' := by
    intro T _ _ Γ s s' h
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [valAt_top, map_sub, h, sub_self]
  have mem_top_iff : ∀ {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → R), f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    intro T _ _ Γ f
    have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
        (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
      intro B _ X x U hx a b
      simp only [valAt, map_sub]
    constructor
    · intro hf t
      rw [Twhopf.mem_order] at hf
      have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
          ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
            valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
        fun g => hf t g (by simp)
      choose U hgU s hs using hreg
      obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
        (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
          intro g g'
          rw [← sub_eq_zero]
          apply Twhopf.sec_inj R T Γ _ _
          intro h hh
          have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
          have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
            (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
          refine (hsub _ _ hh _ _).trans ?_
          erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
          rw [hs, hs, sub_self])
      refine ⟨g0, fun h => ?_⟩
      have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
      let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
      have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
        Twhopf.top_le_of_mem _ z (hgU _)
      refine (valAt_top _ htop g0).symm.trans ?_
      refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
      erw [hglue ((Γ.pt h).left z)]
      exact hs _ h hh
    · intro hf
      rw [Twhopf.mem_order]
      intro t g _
      obtain ⟨s, hs⟩ := hf t
      unfold QFGroup.RegularAt
      exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩
  ext f
  rw [quotOrder, Subalgebra.mem_comap, mem_top_iff, mem_top_iff]
  constructor
  · intro hf t
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank R T Γ
    obtain ⟨s0, hs0⟩ := (mem_top_iff Γ _).1 (hd (fun x => f (t * x))) 1
    obtain ⟨h0, rfl⟩ := hα t
    obtain ⟨s₁, hs₁⟩ := hf h0
    have key : a.left.appTop s0 = a.left.appTop (pb Γ.G.hom d) * s₁ := by
      apply sec_ext Γ₁
      intro h
      rw [map_mul, ← val_comp, ← val_comp, ← Over.comp_left, hpt h, hs0, val_pb (Over.w (Γ.pt (α h))), hs₁, ← map_mul]
      congr 1
      show d * f (α h0 * (1 * α h)) = d * f (α (h0 * h))
      rw [_root_.one_mul, MonoidHom.map_mul]
    have e : Spec.map a.left.appTop = Γ₁.G.left.isoSpec.inv ≫ a.left ≫ Γ.G.left.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have hff : a.left.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff _).1 ⟨by rw [e]; infer_instance, by rw [e]; infer_instance⟩
    letI : Algebra Γ(Γ.G.left, ⊤) Γ(Γ₁.G.left, ⊤) := a.left.appTop.hom.toAlgebra
    have hmem : s0 ∈ Ideal.span {pb Γ.G.hom d} := by
      rw [← @Ideal.comap_map_eq_self_of_faithfullyFlat _ _ _ _ _ hff (Ideal.span {pb Γ.G.hom d}),
        Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s₁, key⟩
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨s, fun h => ?_⟩
    have e3 := hs0 h
    rw [← hs, map_mul, val_pb (Over.w (Γ.pt h))] at e3
    have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hd0
    apply mul_right_cancel₀ hd'
    rw [e3, ← map_mul]
    congr 1
    show d * f (α h0 * (1 * h)) = f (α h0 * h) * d
    rw [_root_.one_mul, mul_comm]
  · intro hf h0
    obtain ⟨s, hs⟩ := hf (α h0)
    refine ⟨a.left.appTop s, fun h => ?_⟩
    rw [← val_comp, ← Over.comp_left, hpt h, hs]
    exact congrArg _ (congrArg f (map_mul α h0 h).symm)

end PositivityTheory.HtPt.Mh
end
end

