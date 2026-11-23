module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartCount
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private noncomputable def jet {σ E : Type} [Field E] (i : σ) : MvPowerSeries σ E →ₐ[E] DualNumber E where
  toFun f := ⟨MvPowerSeries.constantCoeff f, MvPowerSeries.coeff (Finsupp.single i 1) f⟩
  map_one' := by
    classical
    ext
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    classical
    refine TrivSqZeroExt.ext (map_mul MvPowerSeries.constantCoeff f g) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g
    simp [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f g := TrivSqZeroExt.ext (map_add MvPowerSeries.constantCoeff f g) (map_add (MvPowerSeries.coeff _) f g)
  commutes' c := by
    classical
    ext <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, TrivSqZeroExt.algebraMap_eq_inl]

private theorem snd_mul_left {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (A.map (algebraMap E (DualNumber E)) * X).map TrivSqZeroExt.snd = A * X.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum]

private theorem snd_mul_right {E : Type} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E)
    (X : Matrix (Fin 3) (Fin 3) (DualNumber E)) :
    (X * A.map (algebraMap E (DualNumber E))).map TrivSqZeroExt.snd = X.map TrivSqZeroExt.snd * A := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, mul_comm]

private theorem exists_coc {G E : Type} [Group G] [CommRing E]
    (r : G →* GG (m := 3) (R := E)) (r' : G →* GG (m := 3) (R := DualNumber E))
    (h1 : ∀ g, (r' g).right = (r g).right) (h2 : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b) :
    ∃ γ, IsCoc r γ ∧ DualDef r γ r' := by
  obtain ⟨γ, -, hc, hd⟩ := exists_isCoc (RingHom.ker (TrivSqZeroExt.fstHom E E E))
    ((GG.map (algebraMap E (DualNumber E))).comp r) r' (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx', hy']) (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => by
      refine Ideal.Quotient.eq.2 ?_
      show ((r' g).mat a b - algebraMap E (DualNumber E) ((r g).mat a b)).fst = 0
      simp [h2, TrivSqZeroExt.algebraMap_eq_inl])) (h1 g))
  refine ⟨fun g => (γ g).map TrivSqZeroExt.snd, fun g h => ?_, fun g => ⟨h1 g, fun a b => ?_⟩⟩
  · have e : adRep ((GG.map (algebraMap E (DualNumber E))).comp r) g (γ h) =
        (r g).mat.map (algebraMap E (DualNumber E)) * (if (r g).right = 1 then γ h else thetaLie (γ h)) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).map (algebraMap E (DualNumber E)) := rfl
    have e' : ∀ X, adRep r g X = (r g).mat * (if (r g).right = 1 then X else thetaLie X) *
          (((r g).left⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := fun X => rfl
    show (γ (g * h)).map _ = _
    rw [hc g h, Matrix.map_add _ TrivSqZeroExt.snd_add, e, e', snd_mul_right, snd_mul_left]
    split_ifs
    · rfl
    · unfold thetaLie
      rw [Matrix.map_neg _ TrivSqZeroExt.snd_neg, ← Jmat_map (algebraMap E (DualNumber E)), snd_mul_right, snd_mul_left]
      rfl
  · refine TrivSqZeroExt.ext (h2 g a b) ?_
    have e : (r' g).mat = (1 + γ g) * (r g).mat.map (algebraMap E (DualNumber E)) := (hd g).2
    have e2 := congrArg (fun X : Matrix (Fin 3) (Fin 3) (DualNumber E) => X.map TrivSqZeroExt.snd a b) e
    simp only [snd_mul_right] at e2
    refine e2.trans ?_
    show _ = ((γ g).map TrivSqZeroExt.snd * (r g).mat) a b
    refine congrArg (fun X : Matrix (Fin 3) (Fin 3) E => (X * (r g).mat) a b) ?_
    ext c d
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Loc.chartCount :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∀ (n : ℕ) (w : Fin n → ℤ) (φ : U.R →ₐ[O] MvPowerSeries (Fin n) E) (u : Fin n → GQ l × Fin 3 × Fin 3), UpperTheory.V.Loc.IsCompl (D.It U) x φ → (∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart E w (wt a b)) → (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (φ ((U.r.hom (u i).1).mat (u i).2.1 (u i).2.2)) = if i = j then 1 else 0) → ∀ j, Nat.card {i // w i = j} ≤ locDims j := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx n w φ u hφ hg hu j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hxe : ∀ g a b, algebraMap O E (x ((U.r.hom g).mat a b)) = (D.rz E g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG (m := 3) (R := O) => algebraMap O E ((r g).mat a b)) hx
  let d : GQ l → Fin 3 → E := fun g b => algebraMap O E ((D.Ψ g ^ wt1 b : Oˣ) : O)
  have hd : ∀ g, (D.rz E g).mat = Matrix.diagonal (d g) := fun g =>
    Matrix.diagonal_map (map_zero (algebraMap O E))
  have hdd : ∀ g b, d g b * d g⁻¹ b = 1 := fun g b => by
    simp only [d]
    rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul]
    simp
  have hdc : ∀ b, Continuous fun g => d g b := fun b => by
    have := (ptCont (l := l) U.R E ((Algebra.ofId O E).comp x)).1 _ _ (U.r.cont b b)
    refine Continuous.congr this fun g => (hxe g b b).trans ?_
    rw [hd, Matrix.diagonal_apply_eq]
  have key : ∀ i, ∃ γ ∈ finiteCocycles (MonoidHom.id _) (adRep (D.rz E)), ∀ g a b,
      γ g a b = MvPowerSeries.coeff (Finsupp.single i 1) (φ ((U.r.hom g).mat a b)) * d g⁻¹ b := fun i => by
    let F : U.R →ₐ[O] DualNumber E := ((jet i).restrictScalars O).comp φ
    obtain ⟨γ, hc, hγ⟩ := exists_coc (D.rz E) (push F U.r.hom) (fun g => U.r.hasMult g)
      (fun g a b => (hφ.const _).trans (hxe g a b))
    have he : ∀ g a b, γ g a b = (F ((U.r.hom g).mat a b)).snd * d g⁻¹ b := fun g a b => by
      have : (F ((U.r.hom g).mat a b)).snd = (γ g * (D.rz E g).mat) a b :=
        congrArg TrivSqZeroExt.snd ((hγ g).2 a b)
      rw [this, hd, Matrix.mul_diagonal, mul_assoc, hdd, mul_one]
    refine ⟨γ, (rtTangent hP D U E γ ⟨?_, hc⟩ _ hγ).1 ⟨F, rfl, fun y hy => ?_⟩, he⟩
    · refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [he]
      refine Continuous.mul ?_ ((hdc b).comp continuous_inv)
      haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
      have hq := (ptCont (l := l) U.R (DualNumber E) F).1 _ _ (U.r.cont a b)
      letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
      haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
      exact (IsModuleTopology.continuous_of_linearMap
        ((TrivSqZeroExt.sndHom E E).restrictScalars ℚ_[l])).comp hq
    · rw [← hφ.ker, RingHom.mem_ker] at hy
      show jet i (φ y) = 0
      rw [hy, map_zero]
  choose γ hγ he using key
  obtain ⟨hfin, hdim, -⟩ := dim_Z1f_crystalline_deformation hP D E j
  haveI : Module.Finite E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  let v : {i // w i = j} → ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) :=
    fun i => ⟨γ i, hγ i, fun g _ a b hab => by
      rw [he, hg g a b _ (by
        rw [Finsupp.weight_single, one_smul, i.2]
        exact hab.symm), zero_mul]⟩
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := congrArg (fun y : ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E)) ⊓ Submodule.pi Set.univ fun _ => gw E j) =>
      y.1 (u k).1 (u k).2.1 (u k).2.2 * d (u k).1 (u k).2.2) hc
    simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply,
      Matrix.smul_apply, he, hu, smul_eq_mul, Subtype.val_inj] at h1
    simpa [mul_assoc, mul_comm (d (u k).1⁻¹ _), hdd] using h1
  rw [← hdim, Nat.card_eq_fintype_card]
  exact hv.fintype_card_le_finrank
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorAut
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem gg_ext {A : Type} [CommRing A] {x y : GG (m := 3) (R := A)}
    (h : ∀ a b, x.mat a b = y.mat a b)
    (h' : x.right = y.right) : x = y :=
  SemidirectProduct.ext (Units.ext (Matrix.ext h)) h'

private theorem exists_unit {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ t : Oˣ, (t : O) - 1 ∈ maximalIdeal O ∧ Function.Injective fun j : ℤ => t ^ j := by
  have h1 : (maximalIdeal O).comap (algebraMap ℤ_[l] O) = maximalIdeal ℤ_[l] :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal O))
  have h2 : (l : O) ∈ maximalIdeal O := by
    have : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    rw [← h1, Ideal.mem_comap, map_natCast] at this
    exact this
  have h3 : IsUnit (1 - (-(l : O))) := isUnit_one_sub_self_of_mem_nonunits _ (neg_mem h2)
  obtain ⟨t, ht⟩ := h3
  refine ⟨t, by simpa [ht] using h2, injective_zpow_iff_not_isOfFinOrder.2 fun h => ?_⟩
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : (((1 + l) ^ n : ℕ) : O) = ((1 : ℕ) : O) := by
    have := congrArg Units.val e
    rw [Units.val_pow_eq_pow_val, ht] at this
    simpa using this
  have e2 := Nat.cast_injective e1
  have := (Fact.out : l.Prime).pos
  have e3 : 1 < (1 + l) ^ n := Nat.one_lt_pow hn.ne' (by omega)
  omega

theorem UpperTheory.V.Loc.torAut :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → ∃ (t : Oˣ) (θ : U.R →ₐ[O] U.R), (Function.Injective fun j : ℤ => t ^ j) ∧ x.comp θ = x ∧ (∀ a ∈ D.It U, θ a ∈ D.It U) ∧ ∀ g a b, θ ((U.r.hom g).mat a b) = algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := by
  intro hP l _ O _ _ _ _ _ _ _ D U x hx
  obtain ⟨t, ht1, ht⟩ := exists_unit (l := l) O
  have hres : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (j : ℤ),
      res O C (algebraMap O C ((t ^ j : Oˣ) : O)) = 1 := fun C _ _ _ j => by
    have e : Units.map (algebraMap O (ResidueField O) : O →* ResidueField O) t = 1 := by
      apply Units.ext
      have := (residue_eq_zero_iff _).2 ht1
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    have e2 := congrArg Units.val (map_zpow (Units.map (algebraMap O (ResidueField O) : O →* ResidueField O)) t j)
    rw [e, one_zpow] at e2
    rw [AlgHom.commutes]
    exact e2
  have hmat : ∀ (C : Type) [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) g a b,
      (conjBy (tor C (Units.map (algebraMap O C : O →* C) t)) r g).mat a b =
        algebraMap O C ((t ^ wt a b : Oˣ) : O) * (r g).mat a b := fun C _ _ r g a b => by
    rw [(conjBy_tor r _).1, ← map_zpow]
    rfl
  let r' : GLift O D.η D.Ψ U.R :=
    { hom := conjBy (tor U.R (Units.map (algebraMap O U.R : O →* U.R) t)) U.r.hom
      cont := fun a b N => by
        simp only [hmat, map_mul]
        exact (IsLocallyConstant.const _).mul (U.r.cont a b N)
      red := fun g => by
        rw [← U.r.red g]
        refine gg_ext (fun a b => ?_) ((conjBy_tor _ _).2.1 g)
        show res O U.R (GG.mat _ a b) = res O U.R (GG.mat _ a b)
        rw [hmat, map_mul, hres, one_mul] }
  obtain ⟨θ, hθ, -⟩ := (U.rep U.R).2 r' trivial
  have hθm : ∀ g a b, θ ((U.r.hom g).mat a b) =
      algebraMap O U.R ((t ^ wt a b : Oˣ) : O) * (U.r.hom g).mat a b := fun g a b =>
    (congrArg (fun r : GLift O D.η D.Ψ U.R => (r.hom g).mat a b) hθ).trans (hmat _ _ g a b)
  have uniq : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : U.R →ₐ[O] C),
      (∀ g a b, f ((U.r.hom g).mat a b) = f' ((U.r.hom g).mat a b)) → f = f' := fun C _ _ _ f f' h => by
    obtain ⟨F, -, hF⟩ := (U.rep C).2 (U.r.map f') trivial
    refine (hF f ?_).trans (hF f' rfl).symm
    exact GLift.ext (MonoidHom.ext fun g => gg_ext (h g) rfl)
  have hxe : ∀ g a b, x ((U.r.hom g).mat a b) = (r0 D.η D.Ψ g).mat a b := fun g a b =>
    congrArg (fun r : GQ l →* GG (m := 3) (R := O) => (r g).mat a b) hx
  refine ⟨t, θ, ht, uniq O _ _ fun g a b => ?_, fun y hy => ?_, hθm⟩
  · rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
    by_cases hab : a = b
    · simp [hab, wt]
    · rw [hxe, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab, mul_zero]
  · by_cases hI : D.It U = ⊤
    · rw [hI]; trivial
    haveI : Nontrivial (U.R ⧸ D.It U) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsCO O (U.R ⧸ D.It U) := co_quot O U.R _ (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ_surjective O _)
    obtain ⟨f, hf, hfI⟩ := rtConj hP D U (U.R ⧸ D.It U) (push (Ideal.Quotient.mkₐ O _) U.r.hom)
      (tor _ (Units.map (algebraMap O (U.R ⧸ D.It U) : O →* _) t)) (fun a b => by
        rw [← res_eq_zero_iff O, Matrix.sub_apply, tor_val]
        by_cases hab : a = b
        · subst hab
          rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, map_sub, map_one, ← map_zpow]
          exact sub_eq_zero.2 (hres _ _)
        · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab, sub_zero, map_zero])
      ⟨_, rfl, fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha⟩
    have e : f = (Ideal.Quotient.mkₐ O _).comp θ := uniq _ _ _ fun g a b => by
      rw [AlgHom.comp_apply, hθm, map_mul, AlgHom.commutes]
      exact (congrArg (fun r : GQ l →* GG (m := 3) (R := U.R ⧸ D.It U) => (r g).mat a b) hf).trans (hmat _ _ g a b)
    have := hfI hy
    rw [e] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
end

