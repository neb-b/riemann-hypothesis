module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TwistDisc

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem pow_val_apply (χ : HChar E) (k : ℕ) (x : _) : (χ ^ k).1 x = χ.1 x ^ k := rfl

theorem chiInf_pow (χ : HChar E) (k : ℕ) (z : (Cinf E)ˣ) : chiInf (χ ^ k) z = chiInf χ z ^ k := rfl

theorem dchi_pow (χ : HChar E) (k : ℕ) : dchi (χ ^ k) = (k : ℝ) • dchi χ := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  have h1 : dchi χ = L := fderiv_extZero (continuous_chiInf χ) hL
  have h2 : dchi (χ ^ k) = (k : ℝ) • L := fderiv_extZero (continuous_chiInf (χ ^ k)) fun z => by
    rw [chiInf_pow, Units.val_pow_eq_pow_val, hL, ← Complex.exp_nat_mul]
    simp
  rw [h1, h2]

theorem expo_pow (χ : HChar E) (k : ℕ) (τ : E →+* ℂ) : expo (χ ^ k) τ = k * expo χ τ := by
  simp only [expo, dchi_pow, ContinuousLinearMap.smul_apply, Complex.real_smul, Complex.ofReal_natCast]
  ring

theorem chiDet_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ}
    (h : ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v) (t : ℝ) :
    chiDet a μ (splitCentre E a t) = 1 := by
  unfold splitCentre
  rw [chiDet, MonoidHom.comp_apply, det_infGL]
  change chiInf μ _ = 1
  apply Units.ext
  rw [h, Units.val_one]
  refine Finset.prod_eq_one fun v _ => ?_
  have hz : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) v = ((Real.exp t ^ a : ℝ) : ℂ) := by
    simp [Matrix.scalar_apply, Matrix.det_diagonal, expU, Complex.ofReal_exp]
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_self (by exact_mod_cast (by positivity : Real.exp t ^ a ≠ 0)), _root_.one_zpow]

theorem isSqInt_mulChi {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1) {φ : Sm E a}
    (h : IsSqInt φ.1) : IsSqInt (mulChi a χ φ).1 := by
  obtain ⟨h1, μ, 𝓕, hμ, hF, hI⟩ := h
  refine ⟨fun t g => ?_, μ, 𝓕, hμ, hF, ?_⟩
  · simp only [mulChi_apply, map_mul, hs, one_mul, h1]
  · have e : ∀ g, ‖(mulChi a χ φ).1 g‖ₑ = ‖φ.1 g‖ₑ := fun g => by
      have h2 : ‖((chiDet a χ g : ℂˣ) : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, show ‖((chiDet a χ g : ℂˣ) : ℂ)‖ = 1 from hu _, ENNReal.ofReal_one]
      rw [mulChi_apply, enorm_mul, h2, mul_one]
    simp only [e]
    exact hI

theorem isDiscrete_map {χ : HChar E} (hu : χ.IsUnitary) (hs : ∀ t, chiDet a χ (splitCentre E a t) = 1)
    {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) : IsDiscrete (V.map (mulChi a χ).toLinearMap) := by
  refine { aut := ?_, sqInt := ?_, stable := ?_, ne_bot := ?_, irred := ?_ }
  · rintro _ ⟨φ, hφ, rfl⟩
    have h := hV.aut φ hφ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro γ g
      simp [h.left, chiDet_ratGL]
    · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) φ = φ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) (CuspRep.mulChi a χ φ) = CuspRep.mulChi a χ φ
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
        (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ φ).symm⟩
    · have := h.zfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
        Zalg E a)).map (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
      exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
    · intro g
      obtain ⟨C, N, h1⟩ := h.growth g
      obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
      refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
      change ‖(CuspRep.mulChi a χ φ).1 (g * infGL E a y)‖ ≤ _
      rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
      refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
        ((norm_nonneg _).trans (h1 y))).trans_eq ?_
      ring
  · rintro _ ⟨φ, hφ, rfl⟩
    exact isSqInt_mulChi hu hs (hV.sqInt φ hφ)
  · rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (hV.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  · intro h
    exact hV.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  · intro W hW hW'
    have h := hV.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hW' o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isLocCompGL_map (χ : HChar E) {V : Submodule ℂ (Sm E a)} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ) :
    IsLocCompGL (V.map (mulChi a χ).toLinearMap) w
      (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) := by
  obtain ⟨f, h0, hV, hf⟩ := h
  refine ⟨(mulChi a χ).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (mulChi a χ).injective ?_),
    fun v => ⟨f v, hV v, rfl⟩, fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change mulChi a χ (f (((CuspSub.locDet a χ w g : ℂˣ) : ℂ) • σ.ρ g v)) =
      rt E a (finGL E a (locGL E a w g)) (mulChi a χ (f v))
    rw [map_smul f, hf g v, rt_mulChi, CuspSub.chiDet_locGL]
    simp only [map_smul]
    rfl

theorem hasInfCharGL_map {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ} (h : HasInfCharGL V τ m)
    (χ : HChar E) : HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 3
  ext x
  simp [add_assoc, add_comm, add_left_comm]

end GlobalTheory.BCT.TwistDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedConjDeltaOfUnitModNorms
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.ClSurj

section Theta

variable {R : Type} [CommRing R] {n : ℕ}

theorem Phi_transpose' : (GlobalTheory.Tw.Phi n R)ᵀ = (-1 : R) ^ (n + 1) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · rw [if_pos h, if_pos (by omega), ← pow_add, show n + 1 + i = j + 2 * (i + 1) by omega, pow_add, pow_mul]
    simp
  · rw [if_neg h, if_neg (by omega), mul_zero]

theorem PhiU_inv_val : ((PhiU n R)⁻¹ : GL (Fin n) R).val = (GlobalTheory.Tw.Phi n R)ᵀ := rfl

theorem invT_invT (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  show (((invT n R g)⁻¹ : GL (Fin n) R).val)ᵀ = g.val
  rw [← map_inv]
  show (((g⁻¹)⁻¹ : GL (Fin n) R).val)ᵀᵀ = g.val
  rw [inv_inv, transpose_transpose]

theorem map_invT (c : R →+* R) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (invT n R g) = invT n R (GeneralLinearGroup.map c g) := by
  apply Units.ext
  show c.mapMatrix (((g⁻¹ : GL (Fin n) R).val)ᵀ) = (((GeneralLinearGroup.map c g)⁻¹ : GL (Fin n) R).val)ᵀ
  rw [← map_inv]
  rfl

theorem map_map_self (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin n) R) :
    GeneralLinearGroup.map c (GeneralLinearGroup.map c g) = g :=
  Units.ext (Matrix.ext fun i j => hc (g.val i j))

theorem map_PhiU' (c : R →+* R) : GeneralLinearGroup.map c (PhiU n R) = PhiU n R := by
  apply Units.ext
  ext i j
  change c (GlobalTheory.Tw.Phi n R i j) = GlobalTheory.Tw.Phi n R i j
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem invT_PhiU : invT n R (PhiU n R) = PhiU n R :=
  Units.ext (Matrix.transpose_transpose _)

theorem PhiU_mul_self_val : (PhiU n R * PhiU n R).val = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : GlobalTheory.Tw.Phi n R * (GlobalTheory.Tw.Phi n R)ᵀ = 1 := Phi_mul_transpose n R
  rw [Phi_transpose', Matrix.mul_smul] at h1
  have hs : ((-1 : R) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
  show GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = _
  calc GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1) * (-1) ^ (n + 1)) • (GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R) := by
        rw [hs, one_smul]
    _ = (-1 : R) ^ (n + 1) • (1 : Matrix (Fin n) (Fin n) R) := by rw [mul_smul, h1]

theorem PhiU_sq_central (g : GL (Fin n) R) : g * (PhiU n R * PhiU n R) = (PhiU n R * PhiU n R) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul _ g, PhiU_mul_self_val]
  simp

theorem mul_inv_mul_cancel_comm {G : Type} [Group G] (a b P : G) (hP : ∀ g : G, g * (P * P) = (P * P) * g) :
    (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = a * P := by
  have h : (a * P * b * P⁻¹)⁻¹ * (a * P) * (b * P * a * P⁻¹) = (P * P) * a * P⁻¹ := by group
  rw [h, ← hP a]
  group

end Theta

theorem normId : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (m : ℕ) (y : GL (Fin m) R),
    ((y * thetaGL m c y).val)ᵀ * (invT m R (y * PhiU m R)).val * c.mapMatrix (y * thetaGL m c y).val =
      (invT m R (y * PhiU m R)).val ∧
    c.mapMatrix (invT m R (y * PhiU m R)).val = (-1 : R) ^ (m - 1) • ((invT m R (y * PhiU m R)).valᵀ * (y * thetaGL m c y).val) := by
  intro R _ c hc m y
  have hth : thetaGL m c y = PhiU m R * invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := rfl
  constructor
  · have ht : ((y * thetaGL m c y).val)ᵀ = (invT m R (y * thetaGL m c y)⁻¹).val := by
      show _ = ((((y * thetaGL m c y)⁻¹)⁻¹ : GL (Fin m) R).val)ᵀ
      rw [inv_inv]
    have hm : c.mapMatrix (y * thetaGL m c y).val = (GeneralLinearGroup.map c (y * thetaGL m c y)).val := rfl
    rw [ht, hm, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [hth]
    simp only [map_mul, map_inv, invT_invT, invT_PhiU, map_PhiU', map_invT, map_map_self c hc]
    have := mul_inv_mul_cancel_comm (invT m R y) (GeneralLinearGroup.map c y) (PhiU m R) PhiU_sq_central
    simpa only [mul_assoc] using this
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Subsingleton.elim _ _
    have h1 : c.mapMatrix (invT m R (y * PhiU m R)).val = (invT m R (GeneralLinearGroup.map c y) * PhiU m R).val := by
      show (GeneralLinearGroup.map c (invT m R (y * PhiU m R))).val = _
      rw [map_invT, map_mul, map_PhiU', map_mul, invT_PhiU]
    have h2 : (invT m R (y * PhiU m R)).valᵀ = ((y * PhiU m R)⁻¹).val := transpose_transpose _
    have h3 : (y * PhiU m R)⁻¹ * (y * thetaGL m c y) = invT m R (GeneralLinearGroup.map c y) * (PhiU m R)⁻¹ := by
      rw [hth]; group
    rw [h1, h2, ← Units.val_mul, h3, Units.val_mul, Units.val_mul, PhiU_inv_val, Phi_transpose', Matrix.mul_smul,
      smul_smul, ← pow_add]
    have : m - 1 + (m + 1) = 2 * m := by omega
    rw [this, pow_mul]
    simp
    rfl

theorem exists_twConj_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Separable → aeval u (Q.map e.symm.toRingHom) = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ y : GLw m w, (nrmL m w y).val.charpoly = Q → ∃ x : B.Aˣ, B.σ (x : B.A) = x ∧ ∃ g : GLw m w, y = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g := by
  intro E _ _ _ hE w hw K e he hO hval B m b u Q hQ hu hadj β₀ hβ₀ _ y hy
  have hcc : ∀ z, cj w (cj w z) = z := fun z => by
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← he, ← he, K.c_c]
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hnr : nrmL m w y = y * thetaGL m (cj w) y := by rw [nrmL, if_neg hw]

  have huu : u * B.σ u = 1 := by
    have h := congrArg B.σ hβ₀
    rw [B.σ_σ, map_mul, hβ₀, map_mul, map_pow, map_neg, map_one] at h
    have hε : ((-1 : B.A) ^ (m - 1)) * (-1) ^ (m - 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (β₀ : B.A) * (u * B.σ u) = β₀ * 1 := by
      linear_combination (-1 : B.A) * h - ((β₀ : B.A) * u * B.σ u) * hε
    exact (Units.mul_right_inj β₀).1 h2

  have hQm : Q.Monic := hy ▸ Matrix.charpoly_monic _
  have hQd : Q.natDegree = m := by rw [← hy, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hfin : Module.finrank K.E B.A = Q.natDegree := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin, hQd]
  have hcp := _root_.GlobalTheory.charpoly_mulLeft_eq_map_symm K B _ e u Q hQm hadj hu hfin
  have hU : (GlobalTheory.TwLat.mulMat e b u).charpoly = Q := by
    have : GlobalTheory.TwLat.mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
    rw [this, Matrix.charpoly_map, LinearMap.charpoly_toMatrix, hcp, Polynomial.map_map]
    have hid : (e : K.E →+* w.adicCompletion E).comp e.symm.toRingHom = RingHom.id _ := by
      ext z; simp
    rw [hid, Polynomial.map_id]

  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hP' : B'.P.Separable := by
    show (LinearMap.mulLeft K.E u).charpoly.Separable
    rw [hcp]; exact hQ.map
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := GlobalTheory.UnitLemma.Sandwich.traceForm_nondegenerate B' hP'

  obtain ⟨P, hP⟩ := _root_.GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable _ m (nrmL m w y).val (GlobalTheory.TwLat.mulMat e b u) (by rw [hy, hU]) (by rw [hy]; exact hQ)
  rw [hnr] at hP
  obtain ⟨hn1, hn2⟩ := normId _ (cj w) hcc m y
  set N := (y * thetaGL m (cj w) y).val with hN
  set U := GlobalTheory.TwLat.mulMat e b u with hUdef
  set Gy := (invT m _ (y * PhiU m _)).val with hGy
  set cm := (cj w).mapMatrix (m := Fin m) with hcm
  let Gu : GLw m w := invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P
  have hPt : (invT m _ P⁻¹).val = P.valᵀ := by
    show ((P⁻¹)⁻¹ : GLw m w).valᵀ = _
    rw [inv_inv]
  have hGu : Gu.val = P.valᵀ * Gy * cm P.val := by
    show (invT m _ P⁻¹).val * Gy * cm P.val = _
    rw [hPt]
  have h1 : Uᵀ * P.valᵀ = P.valᵀ * Nᵀ := by rw [← transpose_mul, ← transpose_mul, hP]
  have h2 : cm P.val * cm U = cm N * cm P.val := by rw [← map_mul, ← map_mul, hP]
  have hinv : Uᵀ * Gu.val * cm U = Gu.val := by
    rw [hGu]
    calc Uᵀ * (P.valᵀ * Gy * cm P.val) * cm U = (Uᵀ * P.valᵀ) * Gy * (cm P.val * cm U) := by
          simp only [Matrix.mul_assoc]
      _ = P.valᵀ * (Nᵀ * Gy * cm N) * cm P.val := by rw [h1, h2]; simp only [Matrix.mul_assoc]
      _ = P.valᵀ * Gy * cm P.val := by rw [hn1]
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.TwLat.BetaEx.exists_beta E w K e he B m b u hadj huu hnd Gu.val hinv
  have hsym : cm (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * U) := by
    rw [hβ, hGu, map_mul, map_mul, hn2]
    have hcP : cm (P.valᵀ) = (cm P.val)ᵀ := rfl
    have hcc' : cm (cm P.val) = P.val := Matrix.ext fun i j => hcc (P.val i j)
    rw [hcP, hcc', transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc, hP]
  have hGunit : IsUnit (GlobalTheory.TwLat.gram e b β) := hβ ▸ Gu.isUnit
  obtain ⟨hσβ, hβu⟩ := _root_.GlobalTheory.TwLat.betaSym E w K e he B m b u β hnd hGunit hsym
  refine ⟨β₀⁻¹ * hβu.unit, ?_, P⁻¹, ?_⟩
  · have hi : (((β₀⁻¹ : B.Aˣ) : B.A)) * β₀ = 1 := by simp
    have hi' : B.σ (β₀ : B.A) * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul]; simp
    rw [hβ₀] at hi'
    simp only [Units.val_mul, IsUnit.unit_spec, map_mul, hσβ]
    linear_combination (β * ((β₀⁻¹ : B.Aˣ) : B.A)) * hi' - (β * B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((-1) ^ (m - 1) * u)) * hi
  · have hb : (β₀ : B.A) * ((β₀⁻¹ * hβu.unit : B.Aˣ) : B.A) = β := by simp
    rw [hb, GlobalTheory.TwLat.dlt, dite_eq_left hGunit, hth]
    have hGe : hGunit.unit = Gu := Units.ext (by rw [IsUnit.unit_spec, hβ])
    rw [hGe]
    have hII : ∀ g : GLw m w, invT m _ (invT m _ g) = g := fun g => by
      apply Units.ext
      show (((invT m _ g)⁻¹ : GLw m w).val)ᵀ = g.val
      rw [← map_inv]
      show (((g⁻¹)⁻¹ : GLw m w).val)ᵀᵀ = g.val
      rw [inv_inv, transpose_transpose]
    have hth' : ∀ g : GLw m w, thetaGL m (cj w) g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ :=
      fun g => rfl
    show y = P⁻¹⁻¹ * (invT m _ (invT m _ P⁻¹ * invT m _ (y * PhiU m _) * GeneralLinearGroup.map (cj w) P) * (PhiU m _)⁻¹) *
      thetaGL m (cj w) P⁻¹
    rw [hth', map_mul, map_mul, hII, hII, map_inv, map_inv]
    group

end GlobalTheory.TwLat.ClSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorus
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section
namespace GlobalTheory.KapOrb

theorem exists_unitary_of_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w K e B u x n γ ψ hψ s hs
  obtain ⟨hsl, hu, hh⟩ := hψ
  have hs' : (s : B.A) * B.σ (s : B.A) = 1 := hs
  let Lm : B.A → (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) := fun a =>
    { toFun := fun v => ψ (a * ψ.symm v)
      map_add' := by intro v v'; simp [mul_add]
      map_smul' := by
        intro c v
        have h1 : ψ.symm (c • v) = e.symm c • ψ.symm v := by
          apply ψ.injective
          rw [ψ.apply_symm_apply, hsl, ψ.apply_symm_apply, e.apply_symm_apply]
        simp only [RingHom.id_apply]
        rw [h1, Algebra.mul_smul_comm, hsl, e.apply_symm_apply] }
  have hLm : ∀ a y, Lm a (ψ y) = ψ (a * y) := by
    intro a y; simp [Lm]
  have hLmul : ∀ a b, Lm a ∘ₗ Lm b = Lm (a * b) := by
    intro a b; ext v; simp [Lm, mul_assoc]
  have hLone : Lm 1 = LinearMap.id := by
    ext v; simp [Lm]
  let h : GLw n w :=
    ⟨LinearMap.toMatrix' (Lm (s : B.A)), LinearMap.toMatrix' (Lm ((s⁻¹ : B.Aˣ) : B.A)),
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.mul_inv, hLone, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.inv_mul, hLone, LinearMap.toMatrix'_id]⟩
  have hmv : ∀ v, h.val *ᵥ v = Lm (s : B.A) v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hpres : ∀ v v', stdH w (h.val *ᵥ v) (h.val *ᵥ v') = stdH w v v' := by
    intro v v'
    obtain ⟨y, rfl⟩ := ψ.surjective v
    obtain ⟨z, rfl⟩ := ψ.surjective v'
    rw [hmv, hmv, hLm, hLm, hh, hh]
    congr 1
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 1
    rw [map_mul]
    calc x * ((s : B.A) * y) * (B.σ (s : B.A) * B.σ z) = x * y * B.σ z * ((s : B.A) * B.σ (s : B.A)) := by ring
      _ = x * y * B.σ z := by rw [hs', mul_one]
  refine ⟨h, ?_, ?_, ?_⟩
  · unfold UL
    split_ifs
    · exact Subgroup.mem_top _
    · show cT (cj w) h.val * 1 * h.val = 1
      ext i j
      have hp := hpres (Pi.single j 1) (Pi.single i 1)
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hp
      rw [Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply]
      simp only [stdH, Matrix.transpose_apply, Matrix.col_apply] at hp
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_congr rfl (fun k _ => mul_comm (cj w (h.val k i)) (h.val k j)), hp]
      by_cases hij : i = j
      · subst hij; simp [Pi.single_apply]
      · rw [if_neg hij, Finset.sum_eq_zero]
        intro k _
        by_cases hk : k = j
        · subst hk; simp [Pi.single_apply, Ne.symm hij, hij]
        · simp [Pi.single_apply, hk]
  · apply Units.ext
    apply Matrix.toLin'.injective
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := ψ.surjective v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hu, hmv, hmv, hLm, hLm, ← hu, mul_left_comm]
  · intro y
    rw [hmv, hLm]

end GlobalTheory.KapOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_valuationSubring_ratFunc_residue_X_eq_zero :
    ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  intro k _
  let v := (Polynomial.idealX k).valuation (RatFunc k)
  have hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
    exact (Polynomial.idealX k).valuation_le_one _
  have hX : v RatFunc.X < 1 := by
    rw [← RatFunc.algebraMap_X]
    exact ((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by
      rw [Polynomial.idealX_span]; exact Ideal.mem_span_singleton_self _)
  have hX' : RatFunc.X ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact hX.le
  refine ⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc,
    ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩
  · ext a; rfl
  · rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationSplitUnitarySchwartzBruhStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  first | exact @GlobalTheory.KSp.Exist.exists_isKW | exact GlobalTheory.KSp.Exist.exists_isKW | (intros; apply GlobalTheory.KSp.Exist.exists_isKW <;> assumption)
end

