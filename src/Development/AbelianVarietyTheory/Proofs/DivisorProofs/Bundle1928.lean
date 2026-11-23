module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwines
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open GlobalTheory.LatVac GlobalTheory.MixedForm
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitScalX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem lin_zero_basis (h : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (χX χW : Chr F E)
    (om : Rep σ X W) (hW : M.IsWeil ψ χX χW om) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t b c ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (y : (Fv F v)ˣ) (hy : (y : Fv F v) = ((mat g).map (piW (t.comp σ))).det)
    (φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ι φ₁ 0 = (chrW χW (t.comp σ) y : ℂ) * ((GlobalTheory.SplitWeil.nabs (Fv F v) y ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ι φ 0 := by
  obtain ⟨Λ, hΛ, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨φ₂, hφ₂, rfl⟩ := hι.bij.surjOn hf
  refine form_scalar h M ψ χX χW om hW t (LinearMap.proj 0 ∘ₗ ι) (conjForm (Λ ∘ₗ ι)) (fun w hw φ hφ => ?_)
    (fun w hw φ hφ => ?_) (star φ₂) (star_mem_SB hφ₂) ?_ g hg y hy φ φ₁ hφ hA
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.mult u hu ((e2 t).trans hw) φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ) 0 (fun a _ => smul_zero a) (Matrix.map_zero _ (map_zero _))
    rw [e1] at this
    simpa [symp, hTens] using this
  · obtain ⟨u, hu, e1, e2⟩ := exists_at (v := v) M w
    have := hι.trans u hu ((e2 _).trans hw) _ (star_mem_SB hφ) _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ _ (star_mem_SB hφ))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu _)
    rw [e1] at this
    change star (Λ (ι _)) = star (Λ (ι _))
    rw [star_schr (psiAt ψ v) (fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _), funext this,
      hΛ _ (hι.bij.mapsTo (star_mem_SB hφ))]
  · change star (Λ (ι (star (star φ₂)))) ≠ 0
    rwa [star_star, star_ne_zero]

theorem chrW_comp_conj (h : IsCMExt F E σ) {K : Subgroup (AF F)ˣ} {χ : Chr F E} {m : ℕ} (hχ : ResEtaPow K χ m)
    (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW χ (t.comp σ) x = (chrW χ t x)⁻¹ := by
  obtain ⟨ε, e1, e2, e3, e4, e5, e6, e7⟩ := exists_idem h t
  have e8 : piW (t.comp σ) ε = 0 := by simpa [e7] using congrArg (piW (t.comp σ)) e2
  have key : ∀ a a' : Fv F v, a * a' = 1 → (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a - 1))) *
      (1 + ε * algebraMap (AF F) (AE F E) (liftV v (a' - 1))) = 1 := fun a a' haa => by
    have e : liftV v (a - 1) + liftV v (a' - 1) + liftV v (a - 1) * liftV v (a' - 1) = 0 := by
      rw [liftV_mul, evFin_liftV, ← map_add (f := _), ← map_add (f := _), show a - 1 + (a' - 1) + (a - 1) * (a' - 1) = 0 by
        linear_combination haa, map_zero]
    have e' := congrArg (algebraMap (AF F) (AE F E)) e
    rw [map_add (f := _), map_add (f := _), map_mul, map_zero] at e'
    linear_combination ε * e' + algebraMap (AF F) (AE F E) (liftV v (a - 1)) *
      algebraMap (AF F) (AE F E) (liftV v (a' - 1)) * e1
  have hat : ∀ a : Fv F v, At (evFin F v) (1 + ε * algebraMap (AF F) (AE F E) (liftV v a) - 1) := fun a u hu => by
    rw [add_sub_cancel_left, ← mul_smul_comm, Algebra.smul_def, ← map_mul,
      show u * liftV v a = 0 from at_liftV v a u hu, map_zero, mul_zero]
  let z : (AE F E)ˣ := ⟨_, _, key _ _ x.mul_inv, key _ _ x.inv_mul⟩
  have hz : At (evFin F v) ((z : AE F E) - 1) := hat _
  have hzi : At (evFin F v) (((z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := hat _
  have z1 : piW t (z : AE F E) = x := by
    change piW t (1 + _) = _
    rw [map_add (f := _), map_mul, map_one, e5, piW_algebraMap, evFin_liftV]; ring
  have z2 : piW (t.comp σ) (z : AE F E) = 1 := by
    change piW _ (1 + _) = _
    rw [map_add (f := _), map_mul, map_one, e8, zero_mul, add_zero]
  obtain ⟨n1, n2⟩ := GlobalTheory.T.local_norm_unramified_factorization F E σ h v t z hz
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) z with ha
  have n1' : At (evFin F v) ((a : AF F) - 1) := n1
  have n2' : evFin F v (a : AF F) = x := by rw [← mul_one (x : Fv F v), ← z1, ← z2]; exact n2
  have h1 := hχ a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩)), Circle.coe_eq_one] at h1
  set A : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a with hA
  have hAv : (A : AE F E) = algebraMap (AF F) (AE F E) a := rfl
  have w0 : At (evFin F v) (((A * z⁻¹ : (AE F E)ˣ) : AE F E) - 1) := fun u hu => by
    have a1 : u • ((A : AE F E) - 1) = 0 := by
      rw [hAv, ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul,
        show u * ((a : AF F) - 1) = 0 from n1' u hu, map_zero]
    rw [Units.val_mul, show (A : AE F E) * (z⁻¹ : (AE F E)ˣ) - 1 =
      ((A : AE F E) - 1) * (z⁻¹ : (AE F E)ˣ) + ((z⁻¹ : (AE F E)ˣ) - 1) by ring, smul_add, ← smul_mul_assoc, a1,
      hzi u hu, zero_mul, add_zero]
  have zz : ∀ τ : E →ₐ[F] Fv F v, piW τ ((A * z⁻¹ : (AE F E)ˣ) : AE F E) * piW τ (z : AE F E) = x := fun τ => by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right, hAv, piW_algebraMap, n2']
  have w1 : piW t ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
    have := zz t
    rw [z1] at this
    exact (mul_eq_right₀ x.ne_zero).1 this
  have w2 : piW (t.comp σ) ((A * z⁻¹ : (AE F E)ˣ) : AE F E) = x := by
    have := zz (t.comp σ)
    rwa [z2, mul_one] at this
  have c1 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v t z hz z2
  have c2 := GlobalTheory.T.local_character_norm_one_unit F E σ h χ v (t.comp σ) (A * z⁻¹) w0 (by rw [comp_conj_conj h]; exact w1)
  rw [show Units.map (piW t).toMonoidHom z = x from Units.ext z1] at c1
  rw [show Units.map (piW (t.comp σ)).toMonoidHom (A * z⁻¹) = x from Units.ext w2] at c2
  rw [c1, c2, map_mul, h1, one_mul, map_inv, map_inv]

theorem scalar_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ X.J → ℂ, (∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = κ g • fun Y => ι φ (((locMat t b g)⁻¹ : GL (Fin n) (Fv F v)).val * Y)) →
    ∀ g ∈ UAt σ X (evFin F v), κ g = (chrW χW t (GlobalTheory.SplitFlip.gdet (locMat t b g)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t b g)) (-(d : ℂ) / 2) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hT v t b c ι hι κ hκ g hg
  have h := hT.base.cm
  have hJ : (X.J.map t).det ≠ 0 := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.herm.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn (indicator_intM_mem_SB (k := Fv F v) (R := Fin n) (D := Fin d))
  have hφ0 : ι φ 0 ≠ 0 := by
    rw [e, Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) (Fv F v)) ∈ intM (Fv F v) (Fin n) (Fin d) from
      fun _ _ => zero_mem _)]
    exact one_ne_zero
  set x : (Fv F v)ˣ := GlobalTheory.SplitFlip.gdet (locMat t b g) with hx
  have hx1 : (x : Fv F v) = ((mat g).map (piW t)).det := by
    change (locMat t b g).val.det = _
    rw [locMat_val, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one,
      one_mul]
  have hx2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    have hu := congrArg Matrix.det (GlobalTheory.Div.CoordOpp.unit_map σ g t)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hx1, mul_right_comm, mul_eq_right₀ hJ] at hu
    exact Units.inv_eq_of_mul_eq_one_right hu
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ M _ _ om _ _ _ _ hT v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero_basis h M B.ψ hT.base.std _ _ om hT.weil t b c ι hι g hg _ hx2 φ φ₁ hφ hA
  rw [hκ g hg φ hφ φ₁ hφ₁ hA, chrW_comp_conj h hT.resW, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) x⁻¹ ^ ((d : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow x (-(d : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _)]
    push_cast
    rfl
  rw [k2] at k1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_zero] at k1
  exact mul_right_cancel₀ hφ0 k1

end GlobalTheory.SplitScalX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

theorem isUnit_det_dbl_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : J.det ≠ 0) :
    IsUnit ((dbl J).map t).det := by
  have e : ((dbl J).map t).det = (t : E →+* Fv F v) (dbl J).det := by
    rw [RingHom.map_det]; rfl
  rw [e, isUnit_iff_ne_zero]
  have hd : (dbl J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hJ (mul_ne_zero (pow_ne_zero _ (by simp)) hJ)
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hd

theorem unitary_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (X : UD σ J) :
    ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t))ᵀ * (dbl J).map t *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) = (dbl J).map t := by
  have hX : (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J) := X.2
  have h := congrArg (fun M => M.map (piW t)) hX
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have eD : (dbl (incM F J)).map (piW t) = (dbl J).map t := by
    ext (i | i) (j | j) <;> simp [dbl, incM, GlobalTheory.Div.CoordOpp.piW_inclR]
  have eC : ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ)).map (piW t) =
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) := by
    ext i j; simp [GlobalTheory.Div.CoordOpp.piW_cA]
  rw [eD, eC] at h
  simpa [Matrix.transpose_map] using h

end GlobalTheory.DblScal

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.locMatD_injOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  intro F E _ _ _ _ _ σ hcm d J hJ v t c p hp q hq hpq
  set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := p.1.val with hPdef
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := q.1.val with hQdef

  have e0 : (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c =
      (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) q.1 * dsum c := hpq
  have eG := mul_left_cancel (mul_right_cancel e0)
  have h1 : P.map (piW t) = Q.map (piW t) := congrArg Units.val eG

  have h2 : P.map (piW (t.comp σ)) = Q.map (piW (t.comp σ)) := by
    have hUp := unitary_at t p
    have hUq := unitary_at t q
    rw [← hPdef] at hUp
    rw [← hQdef, ← h1] at hUq
    set g := Matrix.GeneralLinearGroup.map (piW t) p.1
    have hg : (g : Matrix _ _ (Fv F v)) = P.map (piW t) := rfl
    have hinv : ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * (P.map (piW t))ᵀ = 1 := by
      rw [← hg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have e1 : (dbl J).map t * P.map (piW (t.comp σ)) = (dbl J).map t * Q.map (piW (t.comp σ)) := by
      have := hUp.trans hUq.symm
      have := congrArg (fun M => ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * M) this
      simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
    have hD := isUnit_det_dbl_map t hJ
    have := congrArg (fun M => ((dbl J).map t)⁻¹ * M) e1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul] using this

  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  have hev : evFin F v (1 - e) = 0 := by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hp' : At (evFin F v) (P - 1) := hp
  have hq' : At (evFin F v) (Q - 1) := hq
  have hM : P - Q = e • (P - Q) := by
    have h0 : (1 - e) • (P - Q) = 0 := by
      have : P - Q = (P - 1) - (Q - 1) := by abel
      rw [this, smul_sub, hp' (1 - e) hev, hq' (1 - e) hev, sub_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine Subtype.ext (Units.ext ?_)
  change P = Q
  rw [← sub_eq_zero, hM]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  apply GlobalTheory.InertVacIso.smul_eq_zero_of_compFin
  apply GlobalTheory.AdelicU.split_ext hcm t
  · change piW t ((P - Q) i j) = splitProj t 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h1 i) j
  · change piW (t.comp σ) ((P - Q) i j) = splitProj (t.comp σ) 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h2 i) j

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConjStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  first | exact @GlobalTheory.OppLinChar.char_eq_psi_symp | exact GlobalTheory.OppLinChar.char_eq_psi_symp | (intros; apply GlobalTheory.OppLinChar.char_eq_psi_symp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  first | exact @GlobalTheory.LagrCoord.exists_coord | exact GlobalTheory.LagrCoord.exists_coord | (intros; apply GlobalTheory.LagrCoord.exists_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransformStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_moment_matrix_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (g : UA σ X.J) (h : UA σ W.J)
    (x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ((mat g).map (piW t))ᵀ * -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (mat g * x * (mat h)ᵀ).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) * (mat h).map (piW t) = -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) := by
  first | exact @GlobalTheory.Div.CoordOpp.coord_opp_conj | exact GlobalTheory.Div.CoordOpp.coord_opp_conj | (intros; apply GlobalTheory.Div.CoordOpp.coord_opp_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem localSpec_fac_of_closedPoint_mem_range (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0})
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X) (hξ : IsOpenImmersion ξ)
    (hc : yb (IsLocalRing.closedPoint S) ∈ Set.range ξ) : ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  have hrange : Set.range yb ⊆ Set.range ξ := by
    rintro _ ⟨x, rfl⟩
    have hsp : x ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint x
    exact (hsp.map yb.base.hom.continuous).mem_open ξ.isOpenEmbedding.isOpen_range hc
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ yb hrange)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInfStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_action_schwartz_inf : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ' : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ' w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ≠ v → φ' w = φ w) ∧ Acts (evFin F v) (om' (g, h)) (φ v) (φ' v) ∧ om' (g, h) (pure f φ) = pure f φ' := by
  first | exact @GlobalTheory.PureStabOne.pure_stab_one | exact GlobalTheory.PureStabOne.pure_stab_one | (intros; apply GlobalTheory.PureStabOne.pure_stab_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.AbInterior

theorem mem_interior_of_mem_abLocus : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (S : Scheme.{0}) (f : S ⟶ Y.X) (G : SAB H S), SABMap G Y.t f → ∀ s : S, s ∈ abLocus G.G → f s ∈ (LogKS.interior Y : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y S f G m s hs
  rw [LogKS.coe_interior]
  exact (OneArcCompare.mem_abLocus_pullback Y.t.semi m.cart.1 s).2 hs

end GlobalTheory.AbInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvalNonnegIff
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem nval_nonneg_iff {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) (x : K') :
    0 ≤ nval V e x ↔ (x ≠ 0 → 0 ≤ vV V x) := by
  by_cases hx : x = 0
  · subst hx; simp [nval_zero]
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast he), zero_mul]
  simp only [ne_eq, hx, not_false_eq_true, forall_const]
  norm_cast

theorem intAt_iff {Xo : Moduli Dw l} {c : Coeff l} (f : Rul Xo c) :
    IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
      evI y f ≠ 0 → 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io y hy hne
    obtain ⟨la, e, ho⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T io hy
    have := h la _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho y hy () trivial, rfl⟩
    exact (nval_nonneg_iff ho.1 _).1 this hne
  · rintro h la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    exact (nval_nonneg_iff ho.1 _).2 (h T ι y hy)

theorem pull_intAt_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → (IntAt d.Xo₂ d.c₂ g ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hO a n f hf g hg hP
  rw [intAt_iff, intAt_iff]
  constructor
  · intro hG T io y hy hne
    obtain ⟨T', iT, e, y', io₂, y₂, ⟨he, hv, φ, hφ, hm⟩, hfin, hio, hover⟩ :=
      GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c 0 d hlev T io y hy
    have h1 : evI y₂ g = evI y' f := by
      letI := (iT.comp io).toAlgebra
      letI := io₂.toAlgebra
      exact GlobalTheory.CoverDown.evR_eq_of_pull hf hg hP (fun a => hio a) hover
    have h2 : evI y' f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      have := GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1
        (GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y.1) y'.1 hm
      show evR Xo c f y'.1 = iT (evR Xo c f y.1)
      rw [this]
      exact DFunLike.congr_fun hφ _
    have key := hG T' io₂ y₂ hfin (by rw [h1, h2]; exact (map_ne_zero iT).2 hne)
    rw [h1, h2, hv] at key
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast he)).1 key
  · intro hF T io₂ y₂ hy hne
    obtain ⟨y, hyalg, -, hval⟩ := GlobalTheory.CoverDown.exists_intFr_below E H Dw l Xo c d hpq hlev hO T io₂ y₂ hy
    rw [hval a n f hf g hg hP] at hne ⊢
    exact hF T _ y hyalg hne

end GlobalTheory.CoverInt
end
end

