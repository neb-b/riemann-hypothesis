module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualInclUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.EbSMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def ebS {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd

private theorem ebS_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    ebS (X * Y) = X.map (dF K) * ebS Y + ebS X * Y.map (dF K) := by
  ext i j
  simp only [ebS, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dF, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_comm]

theorem UpperTheory.V.Ws.Eb.tanOf :
    ∀ {K G : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ' : G →* GL (Fin n) (DualNumber K)), Continuous ρ' →
        Continuous (W.pushRep (dF K) ρ') ∧ ∃ y ∈ Z1 (Loc.adGL (W.pushRep (dF K) ρ')), IsTan (W.pushRep (dF K) ρ') y ρ' := by
  intro K G _ _ _ _ _ _ n ρ' hρ'
  set ρ := W.pushRep (dF K) ρ' with hρ
  have hdF : Continuous (dF K) := TrivSqZeroExt.continuous_fst
  have hv : Continuous fun g => (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_val.comp hρ'
  have hi : Continuous fun g => (↑((ρ' g)⁻¹) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_coe_inv.comp hρ'
  have hc : Continuous ρ := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hdF, hi.matrix_map hdF⟩
  have hci : Continuous fun g => (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv.comp hc
  have e : ∀ g, (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) = (↑(ρ g) : Matrix (Fin n) (Fin n) K) :=
    fun g => rfl
  have hS : Continuous fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    continuous_matrix fun i j => TrivSqZeroExt.continuous_snd.comp (hv.matrix_elem i j)
  refine ⟨hc, fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K),
    ⟨hS.matrix_mul hci, ?_⟩, ?_⟩
  · intro g h
    show ebS (↑(ρ' (g * h)) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ (g * h))⁻¹) : Matrix (Fin n) (Fin n) K) =
      ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) +
        (↑(ρ g) : Matrix (Fin n) (Fin n) K) * (ebS (↑(ρ' h) : Matrix (Fin n) (Fin n) (DualNumber K)) *
          (↑((ρ h)⁻¹) : Matrix (Fin n) (Fin n) K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)
    rw [map_mul, map_mul, Units.val_mul, ebS_mul, e, e, _root_.mul_inv_rev, Units.val_mul, add_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    exact add_comm _ _
  · intro g i j
    show _ = (_, (ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑(ρ g) : Matrix (Fin n) (Fin n) K)) i j)
    rw [Units.inv_mul_cancel_right]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.FlagDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.residue_dual {K : Type} [Field K] (x : DualNumber K) :
    residue (DualNumber K) x = ((residue (DualNumber K)).comp (algebraMap K (DualNumber K))) (dF K x) := by
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have e : x - algebraMap K (DualNumber K) (dF K x) = TrivSqZeroExt.inr x.snd := by
    ext <;> simp [dF, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp

private theorem UpperTheory.V.Ws.Eb.charpoly_lift {A K H : Type} [CommRing A] [CommRing K] [Group H] {n : ℕ} (f : A →+* K)
    (r : H →* GL (Fin n) A) (κ : Fin n → H →* Aˣ) (h : W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i))
    (z : MonoidAlgebra A H) :
    (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) z).charpoly.map f =
      ∏ i, (X - C (f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) z))) := by
  unfold W.HasFlag W.pushRep W.pushCh at h
  obtain ⟨g, hg⟩ := h
  have key : ∀ y : MonoidAlgebra A H,
      (∀ i j : Fin n, j < i → ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i, ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, add_mul, Matrix.add_apply]
      exact ⟨fun i j hij => by rw [hx.1 i j hij, hy.1 i j hij, add_zero], fun i => by rw [hx.2, hy.2]⟩
    | single s a =>
      have e : (g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) (MonoidAlgebra.single s a)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f a • ((g * ((GeneralLinearGroup.map f).comp r) s * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [MonoidAlgebra.lift_single]
        have e' : f.mapMatrix (a • ((r s : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = f a • ((GeneralLinearGroup.map f (r s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          ext i j
          simp [GeneralLinearGroup.map]
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, e', Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
      · rw [Matrix.smul_apply, (hg s).2 i]
        simp [MonoidAlgebra.lift_single]
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv]
  simp only [← RingHom.mapMatrix_apply]
  rw [Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (key z).1 i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(key z).2 i]

theorem UpperTheory.V.Ws.Eb.flagDual :
    ∀ {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ' : H →* GL (Fin n) (DualNumber K)) (κ : Fin n → H →* (DualNumber K)ˣ), (Function.Injective fun i => W.pushCh (dF K) (κ i)) →
        W.HasFlag (W.pushRep (dF K) ρ') (fun i => W.pushCh (dF K) (κ i)) → (∀ g : Fin n → H, (List.ofFn fun i => W.mat ρ' (g i) - algebraMap (DualNumber K) _ (κ i (g i) : DualNumber K)).prod = 0) → W.HasFlag ρ' κ := by
  intro K H _ _ _ n ρ' κ hinj hflag hprod
  set φ : K →+* ResidueField (DualNumber K) := (residue (DualNumber K)).comp (algebraMap K (DualNumber K)) with hφ
  have hres : residue (DualNumber K) = φ.comp (dF K) := RingHom.ext fun x => UpperTheory.V.Ws.Eb.residue_dual x
  have hcard : (n : Cardinal) ≤ Cardinal.mk (ResidueField (DualNumber K)) := by
    haveI : Infinite (ResidueField (DualNumber K)) := Infinite.of_injective φ φ.injective
    exact (Cardinal.natCast_lt_aleph0 (n := n)).le.trans (Cardinal.infinite_iff.mp inferInstance)
  have hinj' : Function.Injective fun i => ((residue (DualNumber K) : DualNumber K →* ResidueField (DualNumber K))).comp ((Units.coeHom (DualNumber K)).comp (κ i)) := by
    intro i j hij
    apply hinj
    ext s
    have hs := DFunLike.congr_fun hij s
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_ofClass] at hs
    rw [hres, RingHom.comp_apply, RingHom.comp_apply] at hs
    have := φ.injective hs
    simpa [W.pushCh] using this
  have hchar : ∀ z : MonoidAlgebra (DualNumber K) H,
      Polynomial.map (residue (DualNumber K))
          ((MonoidAlgebra.lift (DualNumber K) (Matrix (Fin n) (Fin n) (DualNumber K)) H ((Units.coeHom _).comp ρ')) z).charpoly =
        ∏ i, (X - C ((residue (DualNumber K)) ((MonoidAlgebra.lift (DualNumber K) (DualNumber K) H ((Units.coeHom _).comp (κ i))) z))) := by
    intro z
    rw [hres, ← Polynomial.map_map, UpperTheory.V.Ws.Eb.charpoly_lift (dF K) ρ' κ hflag z, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
    rfl
  obtain ⟨z, g, -, -, hg⟩ := AlgebraTools.lemma_L ρ' κ hcard hprod hinj' hchar
  unfold W.HasFlag
  exact ⟨g, hg⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem im_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

private theorem im_model {l : ℕ} [hl : Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {n : ℕ}
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (r : G →* GL (Fin n) (PadicAlgCl l)) (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j)
    (hE : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ E) :
    ∃ (Q : GL (Fin n) (PadicAlgCl l)) (r₀ : G →* GL (Fin n) c.O),
      ∀ g, r g * Q = Q * W.pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  letI : Algebra c.O E := (c.O.val.toRingHom.codRestrict E fun x => ((hc _).1 x.2).1).toAlgebra
  have ha : ∀ x : c.O, ((algebraMap c.O E x : E) : PadicAlgCl l) = x := fun _ => rfl
  haveI : FaithfulSMul c.O E := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    Subtype.ext (congrArg (fun z : E => (z : PadicAlgCl l)) h)
  haveI : IsFractionRing c.O E := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨N, hN⟩ := im_small (l := l) ‖(z : PadicAlgCl l)‖
    refine ⟨⟨(l : PadicAlgCl l) ^ N * z, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) z.2, by rwa [norm_mul]⟩⟩,
      (l : c.O) ^ N, Subtype.ext ?_⟩
    push_cast
    rw [ha]
    field_simp
  let m : G →* Matrix (Fin n) (Fin n) E :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hE g i j⟩
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by
    have h1 : Continuous fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hr i j).norm
    obtain ⟨C, hC⟩ := (isCompact_range h1).bddAbove
    refine ⟨C, fun g i j => le_trans ?_ (hC ⟨g, rfl⟩)⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨N, hN⟩ := im_small (l := l) C
  obtain ⟨Q, r₀, hQ⟩ := UpperTheory.V.Pa.Det.latInt (A := c.O) (F := E) m.toHomUnits ((l : c.O) ^ N)
    (pow_ne_zero _ fun h => hl0 (by simpa using congrArg Subtype.val h)) fun g i j => by
      refine ⟨⟨(l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, (hc _).2
        ⟨mul_mem (pow_mem (natCast_mem _ _) _) (hE g i j), ?_⟩⟩, Subtype.ext ?_⟩
      · rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC g i j) (norm_nonneg _)).trans hN
      · rw [ha]
        push_cast
        rfl
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l)) Q, r₀, fun g => ?_⟩
  have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l))) (hQ g)
  rw [map_mul, map_mul] at h
  convert h using 2 <;> (ext i j; rfl)

private theorem im_cont {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) :
    IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal c.O ^ N) (f g) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  rw [Ideal.Quotient.eq]
  have h2 : ((f y : PadicAlgCl l) - f x) / (l : PadicAlgCl l) ^ N ∈ c.O := (hc _).2
    ⟨div_mem (sub_mem ((hc _).1 (f y).2).1 ((hc _).1 (f x).2).1) (pow_mem (natCast_mem _ _) _), by
      rw [norm_div]
      exact div_le_one_of_le₀ hy.le (norm_nonneg _)⟩
  have h3 : f y - f x = (l : c.O) ^ N * ⟨_, h2⟩ := Subtype.ext (by push_cast; field_simp)
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)

private theorem im_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  refine ⟨IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul ℚ_[l] a y]
      exact IntermediateField.smul_mem _ hy
  · have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
    have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
    rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

theorem UpperTheory.V.Ws.Eb.intModel :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H] {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ →
        ∃ (c' : Coef l) (Q : GL (Fin n) (PadicAlgCl l)) (ρ₀ : H →* GL (Fin n) c'.O), c.O ≤ c'.O ∧ (∀ g, ρ g * Q = Q * W.pushRep (algebraMap c'.O (PadicAlgCl l)) ρ₀ g) ∧ ∀ i j, Alg.AdicCont (maximalIdeal c'.O) fun g => W.mat ρ₀ g i j := by
  intro l _ c H _ _ _ _ _ n ρ hρ
  have hr : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := fun i j =>
    (Units.continuous_val.comp hρ).matrix_elem i j
  obtain ⟨E₁, f₁, m₁⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l H n ρ hr
  obtain ⟨E₂, f₂, m₂⟩ := im_field c
  obtain ⟨c', hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  obtain ⟨Q, r₀, hQ⟩ := im_model (E₁ ⊔ E₂) c' hc ρ hr fun g i j => (le_sup_left : E₁ ≤ _) (m₁ g i j)
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  refine ⟨c', Q, r₀, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ _) (m₂ x hx).1, (m₂ x hx).2⟩, hQ, fun i j N => ?_⟩
  refine im_cont (E₁ ⊔ E₂) c' hc _ ?_ N
  have e : (fun g => ((W.mat r₀ g i j : c'.O) : PadicAlgCl l)) =
      fun g => ((Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := by
    funext g
    rw [← hQ']
    rfl
  rw [e]
  exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i j
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LocLOpen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.locL_cyc (l : ℕ) [Fact l.Prime] :
    Continuous (Loc.cycA l l (PadicAlgCl l)) := by
  have hc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)
  have ha : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map (algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* PadicAlgCl l) ha).comp hc

private theorem UpperTheory.V.Ws.Eb.locL_open {H K ι : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] [Field K] [TopologicalSpace K] [T1Space K] [Finite ι]
    (f : ι → H → K) (hf : ∀ i, Continuous (f i)) (h1 : ∀ i, f i 1 = 1) {k : ℕ} (hk : 0 < k) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ i, ∀ g ∈ U, f i g ^ k = 1 → f i g = 1 := by
  have hfin : ({z : K | z ^ k = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (nthRoots k (1 : K))) fun z hz => ?_
    exact (mem_nthRoots hk).2 hz.1
  have ho : IsOpen (⋂ i, f i ⁻¹' ({z : K | z ^ k = 1} \ {1})ᶜ) :=
    isOpen_iInter_of_finite fun i => hfin.isClosed.isOpen_compl.preimage (hf i)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (Set.mem_iInter.2 fun i h => h.2 (h1 i))
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun i g hg e => ?_⟩
  by_contra hne
  exact Set.mem_iInter.1 (hU hg) i ⟨e, hne⟩

theorem UpperTheory.V.Ws.Eb.locL :
    Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ), ∀ ρ' : H →* GL (Fin n) (DualNumber (PadicAlgCl l)), IsTan ρ y ρ' → ∀ (κ : Fin n → H →* (DualNumber (PadicAlgCl l))ˣ) (m : Fin n → ℤ) (k : ℕ), W.HasFlag ρ' κ → (∀ i j, i < j → m j + 2 ≤ m i) → 0 < k →
        (∀ i g, φ g ∈ Loc.Iq l → (κ i g : DualNumber (PadicAlgCl l)).snd = 0 ∧ (W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) → y ∈ Loc.finiteCocycles φ (Loc.adGL ρ) := by
  intro P l _ H _ _ _ _ _ φ hφ n ρ hρ y hy ρ' ht κ m k hF hm hk hκ
  have hpush : ∀ g, GeneralLinearGroup.map (dF (PadicAlgCl l)) (ρ' g) = ρ g := fun g =>
    Units.ext (Matrix.ext fun a b => congrArg TrivSqZeroExt.fst (ht g a b))
  have hκc : ∀ i, Continuous fun g => (κ i g : DualNumber (PadicAlgCl l)).fst := by
    obtain ⟨h, hh⟩ := hF
    intro i
    have e : (fun g => (κ i g : DualNumber (PadicAlgCl l)).fst) = fun g =>
        ((GeneralLinearGroup.map (dF (PadicAlgCl l)) h * ρ g * (GeneralLinearGroup.map (dF (PadicAlgCl l)) h)⁻¹ :
          GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i i := by
      funext g
      rw [← hpush, ← map_inv, ← map_mul, ← map_mul, ← (hh g).2 i]
      rfl
    rw [e]
    exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i i
  obtain ⟨U, hUo, hU⟩ := locL_open
    (fun i g => ((W.pushCh (dF _) (κ i) g * Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i) : (PadicAlgCl l)ˣ) : PadicAlgCl l))
    (fun i => (hκc i).mul (Units.continuous_val.comp (((locL_cyc l).comp hφ.continuous).zpow (-m i))))
    (fun i => by simp only [map_one, _root_.one_zpow, mul_one, Units.val_one]) hk
  refine Loc.pr6Bar P φ hφ ρ hρ y hy ρ' ht κ m hF (fun i j hij => by have := hm i j hij; omega) U hUo
    (fun i g hg hI => ?_) (fun i j hij => Or.inl (hm i j hij))
  obtain ⟨h0, h1⟩ := hκ i g hI
  have h2 := hU i g hg (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  rw [Units.val_eq_one, _root_.zpow_neg, mul_inv_eq_one] at h2
  rw [← h2]
  exact TrivSqZeroExt.ext rfl h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.psiInj :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
        ∀ {n : ℕ} (κ : Fin n → Dec (F := L) A →* (PadicAlgCl l)ˣ) (m : Fin n → ℤ) (k : ℕ), Function.Injective m → 0 < k → (∀ i (g : Dec (F := L) A), (g : G L Ω) ∈ Ine (F := L) A → (κ i g * cycBar L Ω l g ^ (-m i)) ^ k = 1) → Function.Injective κ := by
  intro l _ L Ω _ _ _ _ _ A w hA hw n κ m k hm hk h i i' e
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA hw
  obtain ⟨-, φ, b1, -, -, b4, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩ := (Loc.cycInertia l).2 φ.range b1.isOpen_range
  rw [b5] at h2
  have h3 : ¬ IsOfFinOrder (cycBar L Ω l (g : G L Ω)) := fun hf => by
    obtain ⟨N, hN, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    refine h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext
      ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))⟩)
    have h4 := congrArg Units.val h1
    simp [cycBar] at h4 ⊢
    exact h4
  have a1 := h i g ((b4 g).1 hg)
  have a2 := h i' g ((b4 g).1 hg)
  rw [← e] at a2
  have a3 := a1.trans a2.symm
  rw [mul_pow, mul_pow, mul_right_inj, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul] at a3
  have a4 := (injective_zpow_iff_not_isOfFinOrder.2 h3) a3
  have a5 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact hm (neg_injective (mul_right_cancel₀ a5 a4))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelForm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Eb

section
variable {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem rf_star_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.star O R n (MonoidAlgebra.single g a) =
      MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp only [W.GFrame.star, W.GFrame.starOp]
  rw [MonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, MonoidAlgebra.smul_single',
    smul_eq_mul]

private noncomputable def rf_dual (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) :
    F.G₀ →* Matrix (Fin n) (Fin n) K where
  toFun g := ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, map_mul, transpose_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

private theorem rf_dual_apply (K : Type) [CommRing K] [Algebra O K] (n : ℕ) (r : F.G₀ →* GL (Fin n) K) (g : F.G₀) :
    rf_dual F O K n r g = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) • (W.mat r (F.conj g)⁻¹)ᵀ := rfl

end

private theorem rf_rep_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (g : G) (b : R) : W.GDet.repAlg ρ R (MonoidAlgebra.single g b) = b • ρ g := by
  simp only [W.GDet.repAlg]
  rw [MonoidAlgebra.lift_single]
  simp

end UpperTheory.V.Ws.Eb

theorem UpperTheory.V.Ws.Eb.relForm :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [IsLocalRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        ∃ P : GL (Fin n) A, F.IsForm c.O n ρ P := by
  intro l _ F c n r B A _ _ _ f ρ hF hD
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  have hF' : Submodule.span A (Set.range (W.mat ρ)) = ⊤ := hF
  have key : ∀ g : F.G₀, (W.GDet.ofRep (W.mat ρ)).lam 1 (F.star c.O A n (MonoidAlgebra.single g 1)) =
      (W.GDet.ofRep (W.mat ρ)).lam 1 (MonoidAlgebra.single g 1) := by
    intro g
    have h1 := congrArg (f : B.B →+* A) (B.u.P 1 g)
    have hm := (AlgebraTools.Det.mapApi B.u.D (f : B.B →+* A)).2.1 1
    rw [← hm, ← hm] at h1
    have hs := (AlgebraTools.Det.starApi F c.O B.B n).2.2.2.2.2 A f (MonoidAlgebra.single g 1)
    rw [← hs, hD] at h1
    simpa using h1
  have trs : ∀ y, (W.GDet.ofRep (W.mat ρ)).lam 1 y = (W.GDet.repAlg (W.mat ρ) A y).trace := by
    intro y
    have h := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn y
    simpa only [W.GDet.tr] using h
  have hsingle : ∀ g, (W.mat ρ g).trace = (rf_dual F c.O A n ρ g).trace := by
    intro g
    have h := key g
    rw [trs, trs, rf_star_single, rf_rep_single, rf_rep_single] at h
    rw [rf_dual_apply, trace_smul, trace_transpose]
    simpa [trace_smul] using h.symm
  have htr : ∀ x, (W.GDet.repAlg (W.mat ρ) A x).trace = (W.GDet.repAlg (rf_dual F c.O A n ρ) A x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, rf_rep_single, one_smul]
      exact hsingle g
    | add x y hx hy => simp only [map_add (f := _), trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, trace_smul, hx]
  have hsurj : Function.Surjective (W.GDet.repAlg (W.mat ρ) A) := by
    intro M
    have hM : M ∈ Submodule.span A (Set.range (W.mat ρ)) := by
      rw [hF']
      trivial
    have hle : Submodule.span A (Set.range (W.mat ρ)) ≤ LinearMap.range (W.GDet.repAlg (W.mat ρ) A).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [rf_rep_single]⟩
    obtain ⟨x, hx⟩ := hle hM
    exact ⟨x, by simpa using hx⟩
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConjugacy.exists_conj_of_surjective (W.GDet.repAlg (W.mat ρ) A)
    (W.GDet.repAlg (rf_dual F c.O A n ρ) A) hsurj htr
  refine ⟨⟨(↑U : Matrix (Fin n) (Fin n) A)ᵀ, (↑U⁻¹ : Matrix (Fin n) (Fin n) A)ᵀ, ?_, ?_⟩, fun g => ?_⟩
  · rw [← transpose_mul, Units.inv_mul, transpose_one]
  · rw [← transpose_mul, Units.mul_inv, transpose_one]
  · show (W.mat ρ g)ᵀ * (↑U : Matrix (Fin n) (Fin n) A)ᵀ * W.mat ρ (F.conj g) = _
    have h := congrArg transpose (hU (MonoidAlgebra.single g 1))
    rw [rf_rep_single, rf_rep_single, one_smul, one_smul, rf_dual_apply, transpose_mul, transpose_mul,
      transpose_smul, transpose_transpose] at h
    rw [← h, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]
end

