module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DualBaseChangeOfFrobeniusChar
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem ev_not_mem (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EtaCondition
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.GalOfCusp

private theorem eta_val (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

private theorem eta_map (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [eta_val, eta_val]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

private theorem eta_loc {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (v : InfinitePlace F) (hs : χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.locInf v (atInf v k) : ℂˣ) : ℂ) * ((‖v.embedding (k : F)‖ : ℝ) : ℂ) = v.embedding (k : F) := by
  have hv : v.IsReal := IsTotallyReal.isReal v
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion (k : F)) = InfinitePlace.embedding_of_isReal hv k := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm (k : F))
  have hsq : ∀ x : (v.Completion)ˣ, 0 < e x → χ.locInf v x = 1 := fun x hx => by
    have h0 : e.symm (Real.sqrt (e x)) ≠ 0 := by
      rw [map_ne_zero]
      exact (Real.sqrt_pos.2 hx).ne'
    have e1 : x = Units.mk0 _ h0 ^ 2 := Units.ext (e.injective (by
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, e.apply_symm_apply, Real.sq_sqrt hx.le]))
    rw [e1, map_pow]
    exact h2 _
  have h0 : InfinitePlace.embedding_of_isReal hv k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  rw [← InfinitePlace.embedding_of_isReal_apply hv, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · have e1 : atInf v k = -1 * -atInf v k := by simp
    rw [e1, map_mul, hs, hsq _ (by
      rw [Units.val_neg, map_neg]
      exact neg_pos.2 (he ▸ h)), abs_of_neg h]
    simp
  · rw [hsq _ (he ▸ h), abs_of_pos h]
    simp

private theorem eta_inf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (h2 : ∀ x, χ.1 x ^ 2 = 1)
    (hs : ∀ v, χ.locInf v (-1) = -1) (k : Fˣ) :
    ((χ.inf k : ℂˣ) : ℂ) * ((‖∏ φ : F →+* ℂ, φ (k : F)‖ : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ (k : F) := by
  have hb : Function.Bijective fun v : InfinitePlace F => v.embedding :=
    ⟨InfinitePlace.embedding_injective F, fun φ =>
      ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)⟩⟩
  have e1 : χ.inf k = ∏ v : InfinitePlace F, χ.locInf v (atInf v k) := by
    unfold HChar.inf HChar.locInf infDiag
    rw [MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [← hb.prod_comp fun φ => φ (k : F), e1, Units.coe_prod, norm_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => eta_loc χ h2 v (hs v) k

private theorem eta_norm (E : Type) [Field E] [NumberField E] (k : E) :
    ∏ φ : E →+* ℂ, φ k = ((Algebra.norm ℚ k : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

private theorem eta_abs (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ) (k : (maximalRealSubfield E)ˣ) :
    (((GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k : ℂˣ) : ℂ) =
      ((‖∏ φ : maximalRealSubfield E →+* ℂ, φ (k : maximalRealSubfield E)‖ : ℝ) : ℂ) ^ f := by
  have e1 : (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2))).inf k =
      (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).inf (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k) :=
    congrArg (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)).1 (eta_map _ E k)
  rw [e1, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _).2.2]
  simp only [← Complex.ofReal_cpow (norm_nonneg _)]
  rw [← Complex.ofReal_prod, Real.finsetProd_rpow _ _ fun _ _ => norm_nonneg _, ← norm_prod, eta_norm, eta_norm]
  have e2 : Algebra.norm ℚ ((Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom k : Eˣ) : E) =
      Algebra.norm ℚ (k : maximalRealSubfield E) ^ 2 := by
    change Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E k) = _
    rw [← Algebra.norm_norm (S := maximalRealSubfield E), Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow]
  rw [e2, Rat.cast_pow, norm_pow, ← Complex.ofReal_zpow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem UpperTheory.eta_condition :
    Eta := by
  intro E _ _ _ f
  have hq : ∀ x, (quadChar E).1 x ^ 2 = 1 := fun x => by
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  obtain ⟨ξ, m, hm, hξ⟩ := Cq.extReal E
    (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * quadChar E ^ f)⁻¹ (-f) fun k => by
      have e : (quadChar E ^ f).inf k = (quadChar E).inf k ^ f := rfl
      rw [HChar.inf_inv, HChar.inf_mul, Units.val_inv_eq_inv_val, Units.val_mul, eta_abs, e, Units.val_zpow_eq_zpow_val,
        ← mul_zpow, mul_comm, eta_inf _ hq (quadChar_locInf E), Finset.prod_zpow, zpow_neg]
  refine ⟨ξ, m, hm, ?_⟩
  have e : GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ) =
      GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2)) * GlobalTheory.HeightCounting.Blocks.resReal ξ := rfl
  rw [e, hξ, mul_inv, mul_inv_cancel_left, map_inv, map_zpow, compNorm_quadChar, one_zpow, inv_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicRepTwistByCharacter
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulCh {Γ : Type} [Group Γ] (χ : Γ →* ℂˣ) : (Γ → ℂ) ≃ₗ[ℂ] (Γ → ℂ) where
  toFun φ g := (χ g : ℂ) * φ g
  invFun φ g := ((χ g)⁻¹ : ℂˣ) * φ g
  map_add' φ ψ := by ext g; simp [mul_add]
  map_smul' c φ := by ext g; simp [mul_left_comm]
  left_inv φ := by ext g; simp
  right_inv φ := by ext g; simp

private theorem cont_ch {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (χ : Γ →* ℂˣ)
    (h : IsOpen (χ.ker : Set Γ)) : Continuous fun g => (χ g : ℂ) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one χ ?_)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h.mem_nhds χ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.1 hg).symm

private theorem irr_tw {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    ρ.IsIrreducible ↔ (twRep ρ η).IsIrreducible := by
  rw [isIrreducible_iff, isIrreducible_iff]
  refine and_congr_right fun _ => forall_congr' fun W => imp_congr_left ?_
  refine forall_congr' fun g => forall_congr' fun v => forall_congr' fun _ => ?_
  exact (W.smul_mem_iff (Units.ne_zero (η g))).symm

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : UA E n →* ℂˣ)

private theorem RU_mulCh (x : UA E n) (φ : UA E n → ℂ) :
    RU E n x (mulCh χ φ) = (χ x : ℂ) • mulCh χ (RU E n x φ) := by
  ext g
  change (χ (g * x) : ℂ) * φ (g * x) = (χ x : ℂ) * ((χ g : ℂ) * φ (g * x))
  rw [map_mul, Units.val_mul]; ring

private theorem form_mulCh (ho : IsOpen (χ.ker : Set (UA E n))) (hr : ∀ g ∈ ratU E n, χ g = 1) {φ : UA E n → ℂ}
    (h : IsAutFormU φ) : IsAutFormU (mulCh χ φ) := by
  refine ⟨(cont_ch χ ho).mul h.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change (χ (γ * g) : ℂ) * φ (γ * g) = (χ g : ℂ) * φ g
    rw [map_mul, hr γ hγ, one_mul, h.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E n).comp (finU (E := E) (n := n)).subtype) (mulCh χ φ) ?_
    have h2 : IsOpen ((Subtype.val : finU (E := E) (n := n) → UA E n) ⁻¹' (χ.ker : Set (UA E n))) := ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset ((h.level.inter h2).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E n 1 φ = φ
      simp
    · exact χ.ker.one_mem
    · have h1 : RU E n k φ = φ := hk.1
      have h3 : χ k = 1 := hk.2
      change RU E n k (mulCh χ φ) = mulCh χ φ
      rw [RU_mulCh, h1, h3]; simp
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (mulCh χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k (mulCh χ φ) ∈ _
    rw [RU_mulCh]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))
end

theorem UpperTheory.exists_automorphicRep_twist_by_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (χ : UA E n →* ℂˣ), IsOpen (χ.ker : Set (UA E n)) → (∀ g ∈ ratU E n, χ g = 1) → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∃ σ' : Submodule ℂ (UA E n → ℂ), IsAutRepU σ' ∧ (∀ w : Plc E, (∀ g ∈ locU n w, cLoc w g ∈ GlobalTheory.LFun.KGL w (n := n) → χ g = 1) → IsUnramU σ w → IsUnramU σ' w) ∧ ∀ (Gv : Subgroup (UA E n)) (H M : Type) [Group H] [AddCommGroup M] [Module ℂ M] (p : Gv →* H) (ρ : Representation ℂ H M) (η : H →* ℂˣ), (∀ x : Gv, χ x = η (p x)) → (IsCompAlong σ Gv p ρ ↔ IsCompAlong σ' Gv p (twRep ρ η)) := by
  intro E _ _ _ n χ ho hr σ hσ
  refine ⟨σ.comap (mulCh χ).symm.toLinearMap, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun e => ?_, fun W hW hs => ?_⟩,
    fun w hw ⟨φ, hφ, h0, hf⟩ => ?_, fun Gv H M _ _ _ p ρ η hη => and_congr (irr_tw ρ η) ⟨?_, ?_⟩⟩
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    exact form_mulCh χ ho hr (hσ.aut ψ (by simpa using hφ))
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    rw [RU_mulCh]
    refine Submodule.smul_mem _ _ ?_
    simpa using hσ.stable x ψ (by simpa using hφ)
  · refine hσ.ne_bot (eq_bot_iff.2 fun φ hφ => ?_)
    have : mulCh χ φ ∈ σ.comap (mulCh χ).symm.toLinearMap := by simpa using hφ
    rw [e] at this
    simpa using this
  · have := hσ.irred (W.comap (mulCh χ).toLinearMap) (fun φ hφ => by simpa using hW hφ) fun x φ hφ => by
      have := hs x _ hφ
      change RU E n x (mulCh χ φ) ∈ W at this
      rw [RU_mulCh] at this
      exact (W.smul_mem_iff (Units.ne_zero (χ x))).1 this
    refine this.imp (fun e => eq_bot_iff.2 fun φ hφ => ?_) fun e => le_antisymm hW fun φ hφ => ?_
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ W.comap (mulCh χ).toLinearMap := hφ
      rw [e] at this
      simpa using this
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ σ := by simpa using hφ
      rw [← e] at this
      exact this
  · refine ⟨mulCh χ φ, by simpa using hφ, by simpa using h0, fun x hx hk => ?_⟩
    rw [RU_mulCh, hf x hx hk, hw x hx hk]; simp
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => by simpa using h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · change mulCh χ (f ((η (p x) : ℂ) • ρ (p x) v)) = RU E n x (mulCh χ (f v))
      rw [RU_mulCh, map_smul, map_smul, h2, hη]
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).symm.toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · apply (mulCh χ).injective
      apply smul_right_injective _ (Units.ne_zero (χ x))
      have := h2 x v
      rw [twRep_apply, map_smul, ← hη] at this
      change (χ x : ℂ) • mulCh χ ((mulCh χ).symm (f (ρ (p x) v))) = (χ x : ℂ) • mulCh χ (RU E n x ((mulCh χ).symm (f v)))
      rw [← RU_mulCh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, this]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConjInertiaDiagonalOfIsTypeWD
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (r : G L Ω →* GL (Fin n) (Qbar l)) (χ : Fin n → Ine (F := L) A →* (Qbar l)ˣ) (x : WD h), IsWDOf ι r x → IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x → ∃ g : GL (Fin n) (Qbar l), ∀ t : Ine (F := L) A, ((g * r t * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (χ i t : Qbar l) := by
  intro l _ L Ω _ _ _ _ _ ι n A w h _hl r χ x hWD hType
  classical
  obtain ⟨t, _ht, φ, hφ, N, a, hMon, hFS, hax⟩ := hWD
  obtain ⟨b, hbx, hbN, hbρ⟩ := hType
  have hiso : a.Iso b := WD.mk_eq_mk.mp (hax.trans hbx.symm)
  obtain ⟨e, he1, he2⟩ := hiso
  obtain ⟨_hNnil, U, hUo, hU⟩ := hMon
  obtain ⟨haN, hFS⟩ := hFS
  have htoEnd : ∀ X : Matrix (Fin n) (Fin n) (Qbar l),
      toEndC ι X = Matrix.toLin' (X.map ι) := fun X => rfl
  have haN0 : a.N = 0 := by
    apply LinearMap.ext
    intro v
    have h0 := he2 v
    rw [hbN, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h0
    exact h0
  have hN0 : N = 0 := by
    have h0 : Matrix.toLin' (N.map ι) = Matrix.toLin' (0 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← htoEnd, ← haN, haN0, map_zero]
    have h2 := Matrix.toLin'.injective h0
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa using h3
  have hpow : ∀ s : Ine (F := L) A, ∃ m : ℕ, 0 < m ∧ s ^ m ∈ U := by
    intro s
    have hUn : (U : Set (Ine (F := L) A)) ∈ nhds (1 : Ine (F := L) A) := hUo.mem_nhds U.one_mem
    obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).mp hUn
    obtain ⟨E, hEfin, hEu⟩ := (krullTopology_mem_nhds_one_iff L Ω u).mp hu
    let f : ℕ → (E →ₐ[L] Ω) := fun k => ((s : G L Ω) ^ k).toAlgHom.comp E.val
    obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
    have key : ∀ i j : ℕ, i < j → f i = f j → s ^ (j - i) ∈ U := by
      intro i j hlt hf
      apply hsub
      apply hEu
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' := congrArg (fun φ : E →ₐ[L] Ω => φ ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply] at hy'
      have hj : (s : G L Ω) ^ j = (s : G L Ω) ^ i * (s : G L Ω) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hj] at hy'
      have hy'' : ((s : G L Ω) ^ i) y = ((s : G L Ω) ^ i) (((s : G L Ω) ^ (j - i)) y) := hy'
      have := ((s : G L Ω) ^ i).injective hy''
      show ((s ^ (j - i) : Ine (F := L) A) : G L Ω) • y = y
      rw [Subgroup.coe_pow]
      exact this.symm
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨j - i, Nat.sub_pos_of_lt hlt, key i j hlt hfij⟩
    · exact ⟨i - j, Nat.sub_pos_of_lt hlt, key j i hlt hfij.symm⟩
  have hrs : ∀ s : Ine (F := L) A,
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) = a.ρ (ineIncl h s) := by
    intro s
    obtain ⟨m, hm, hsm⟩ := hpow s
    have hrm : (r (s : G L Ω)) ^ m = 1 := by
      apply Units.ext
      have h1 := hU _ hsm
      rw [hN0, smul_zero, IsNilpotent.exp_zero] at h1
      rw [← map_pow, ← Subgroup.coe_pow, h1, Units.val_one]
    set f : Module.End ℂ (Fin n → ℂ) :=
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) with hf
    have hfm : f ^ m = 1 := by
      rw [hf, ← htoEnd, ← map_pow, ← Units.val_pow_eq_pow_val, hrm, Units.val_one, map_one]
    have hfss : f.IsSemisimple := by
      apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := Polynomial.X ^ m - Polynomial.C 1)
      · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
      · simp [hfm]
    obtain ⟨hcomm, hnil⟩ := hFS (ineIncl h s)
    have hwd : toEndC ι (wdMat t hφ r N (ineIncl h s)) = f := by
      simp only [wdMat, hN0, smul_zero, IsNilpotent.exp_zero, mul_one]
      rfl
    simp only [hwd] at hcomm hnil
    have hss2 : (f - a.ρ (ineIncl h s)).IsSemisimple :=
      hfss.sub_of_commute hcomm.symm (a.semisimple _)
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss2)
  let P : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e : Module.End ℂ (Fin n → ℂ))
  let Pi : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e.symm : Module.End ℂ (Fin n → ℂ))
  have hPPi : P * Pi = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e : Module.End ℂ (Fin n → ℂ)).comp (e.symm : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  have hPiP : Pi * P = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e.symm : Module.End ℂ (Fin n → ℂ)).comp (e : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  let Φ := ι.symm.toRingHom.mapMatrix (m := Fin n)
  let g : GL (Fin n) (Qbar l) :=
    ⟨Φ P, Φ Pi, by rw [← map_mul, hPPi, map_one], by rw [← map_mul, hPiP, map_one]⟩
  refine ⟨g, fun s => ?_⟩
  have hA : a.ρ (ineIncl h s) = (e.symm : Module.End ℂ (Fin n → ℂ)).comp
      ((b.ρ (ineIncl h s)).comp (e : Module.End ℂ (Fin n → ℂ))) := by
    apply LinearMap.ext
    intro v
    simp [← he1]
  have hR : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι =
      Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P := by
    have h1 := congrArg LinearMap.toMatrix' (hrs s)
    rw [LinearMap.toMatrix'_toLin', hA, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hbρ s,
      LinearMap.toMatrix'_toLin', ← mul_assoc] at h1
    rw [h1]
    rfl
  have hback : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Φ ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
    ext i j
    simp [Φ]
  show Φ P * (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * Φ Pi = _
  rw [hback, hR, ← map_mul, ← map_mul]
  rw [show P * (Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P) * Pi =
      Matrix.diagonal (fun i => ι (χ i s : Qbar l)) by
    rw [← mul_assoc, ← mul_assoc, hPPi, one_mul, mul_assoc, hPPi, mul_one]]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Φ]
  · simp [Φ, Matrix.diagonal_apply_ne _ hij]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDescentToLevelGroupOfUnramified
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.under (𝓞 K) = v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (RingOfIntegers.algebraMap.injective K L)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

private theorem ker_pr_le {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) (K : Subgroup (G L Ω))
    (hK : IsClosed (K : Set (G L Ω)))
    (hI : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      Ine (F := L) A ≤ K) : V.pr.ker ≤ K := by
  have hc : IsClosed ((K.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    (hK.isCompact.image W.continuous_resP).isClosed
  have hN : NS Ω V.S' ≤ (K.map (W.resP L Ω)).normalCore := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.normalCore_isClosed _ hc)
    intro g hg b
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    have hl : IsLift (RingEquiv.refl (W.Lp L)) (b⁻¹).toRingEquiv := fun x => (b⁻¹).commutes x
    have hAA : ∀ x, (b⁻¹).toRingEquiv x ∈ A ↔ x ∈ A.comap (b⁻¹).toRingEquiv.toRingHom := fun x => Iff.rfl
    have h1 : b * g * b⁻¹ ∈ Ine (F := W.Lp L) (A.comap (b⁻¹).toRingEquiv.toRingHom) := conjGal_mem_Ine hl hAA hg
    have hA' : IsPlaceOver (A.comap (b⁻¹).toRingEquiv.toRingHom) v := fun x => by
      rw [← val_lt_one hAA, ← hA x]
      exact Iff.of_eq (congrArg (fun y => A.valuation y < 1) ((b⁻¹).commutes (x : W.Lp L)))
    obtain ⟨t, ht⟩ := s.unr _ _ hA' h1
    obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA'
    refine ⟨t, hI w (by rw [hwv]; exact hv) _ hw ?_, ht⟩
    rw [← ht] at h1
    exact h1
  intro g hg
  have h1 : W.resP L Ω g ∈ NS Ω V.S' := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hg)
  obtain ⟨t, ht, e⟩ := Subgroup.normalCore_le _ (hN h1)
  have : t = g := AlgEquiv.ext fun x => DFunLike.congr_fun e x
  exact this ▸ ht

private theorem pr_surj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

private theorem ker_closed {H k : Type} [Group H] [TopologicalSpace H] [CommRing k] [TopologicalSpace k] [T2Space k] {n : ℕ}
    (r : H →* GL (Fin n) k) (hr : Continuous r) : IsClosed (r.ker : Set H) := by
  have h : (r.ker : Set H) = {g | ∀ i j, (r g).val i j = (1 : Matrix (Fin n) (Fin n) k) i j} :=
    Set.ext fun g => ⟨fun hg i j => by rw [show r g = 1 from hg]; rfl, fun hg => Units.ext (Matrix.ext hg)⟩
  rw [h, Set.setOf_forall]
  refine isClosed_iInter fun i => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun j => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g => (r g).val := Units.continuous_val.comp hr
  exact hv.matrix_elem i j

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.exists_descent_to_level_group_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, r g = 1) → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ ρ.comp V.pr = r ∧ ∀ P, Af.IsPairing s.c r (cycBar L Ω l ^ (1 - (n : ℤ))) P → V.frame.IsForm c.O n ρ P := by
  intro l _ L Ω _ _ _ _ _ _ s n V c r hcont hI
  have hker : V.pr.ker ≤ r.ker :=
    ker_pr_le V _ (ker_closed r hcont) fun w hw A hA t ht => hI w hw A hA t ht
  let ρ : V.frame.G₀ →* GL (Fin n) (Qbar l) := V.pr.liftOfSurjective (pr_surj V) ⟨r, hker⟩
  have hρ : ∀ g, ρ (V.pr g) = r g := fun g => V.pr.liftOfRightInverse_comp_apply _ _ _ g
  refine ⟨ρ, ?_, MonoidHom.ext hρ, fun P hP g => ?_⟩
  · haveI := isClosed_NS Ω V.S'
    have hq : Topology.IsQuotientMap V.pr :=
      (V.pr_cont W.continuous_resP).isClosedMap.isQuotientMap (V.pr_cont W.continuous_resP) (pr_surj V)
    exact hq.continuous_iff.2 (hcont.congr fun g => (hρ g).symm)
  · obtain ⟨t, rfl⟩ := pr_surj V g
    obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    have e1 : V.frame.conj (V.pr t) = V.pr t' := Subtype.ext (by
      show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
      rw [ht', map_mul, map_mul, map_inv])
    have e2 := hP t t' ht'
    have e3 : V.ε (V.pr t).1 = cycZ L Ω l t := DFunLike.congr_fun V.hε (W.resP L Ω t)
    have e4 : V.frame.eps c.O (Qbar l) (V.pr t) = cycBar L Ω l t := by
      refine Units.ext ?_
      show ((algebraMap ℤ_[l] c.O (V.ε (V.pr t).1 : ℤ_[l]ˣ) : c.O) : Qbar l) = _
      rw [e3]
      rfl
    rw [e1, e4]
    show (ρ (V.pr t)).val.transpose * _ * (ρ (V.pr t')).val = _
    rw [hρ, hρ]
    exact e2
end

