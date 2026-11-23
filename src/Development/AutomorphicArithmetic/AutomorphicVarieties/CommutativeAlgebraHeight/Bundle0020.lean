module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem UpperTheory.V.CA.localDimension_eq_height {C : Type} [CommRing C] (x : Ideal C) [x.IsPrime] (p : Ideal C)
    (hp : p ≤ x) [(x.map (Ideal.Quotient.mk p)).IsPrime] :
    dimAt x p = ((x.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  have hsub : Algebra.algebraMapSubmonoid (C ⧸ p) x.primeCompl = (x.map (Ideal.Quotient.mk p)).primeCompl := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      intro h
      apply hb
      exact (Ideal.mem_quotient_iff_mem hp).mp h
    · intro hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨a, fun ha => hy (Ideal.mem_map_of_mem _ ha), rfl⟩
  haveI : IsLocalization.AtPrime (Localization.AtPrime x ⧸ p.map (algebraMap C (Localization.AtPrime x)))
      (x.map (Ideal.Quotient.mk p)) := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    infer_instance
  unfold dimAt
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ _

theorem UpperTheory.V.CA.c3b :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {B C : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing C] [Algebra B C] [Algebra.FiniteType B C] (x : Ideal C) [x.IsMaximal], IsCL O B → x.comap (algebraMap B C) = maximalIdeal B → ∀ (p : Ideal C) [p.IsPrime], p ≤ x → ∃ t : ℕ, Algebra.trdeg (B ⧸ p.comap (algebraMap B C)) (C ⧸ p) = t ∧ dimAt x p = ringKrullDim (B ⧸ p.comap (algebraMap B C)) + t := by
  intro O _ _ _ _ B C _ _ _ _ _ _ x _ hCL hx p _ hp
  set q := p.comap (algebraMap B C) with hq
  have hqm : q ≤ maximalIdeal B := by
    rw [← hx]
    exact Ideal.comap_mono hp
  haveI : IsLocalRing (B ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : FaithfulSMul (B ⧸ q) (C ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  have hcm : IsCMQuot (B ⧸ q) :=
    cl_cmquot O (B ⧸ q) (cl_quot O B (B ⧸ q) (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective hCL)
  have hlt : Algebra.trdeg (B ⧸ q) (C ⧸ p) < Cardinal.aleph0 := by
    open Algebra in exact trdeg_lt_aleph0_of_finiteType
  set t := (Algebra.trdeg (B ⧸ q) (C ⧸ p)).toNat
  have ht : Algebra.trdeg (B ⧸ q) (C ⧸ p) = t := (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  have mapmax : ∀ {R : Type} [CommRing R] (I J : Ideal R), J.IsMaximal → I ≤ J →
      (J.map (Ideal.Quotient.mk I)).IsMaximal := by
    intro R _ I J hJ hIJ
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hJ with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk I 1 ∈ J.map (Ideal.Quotient.mk I) := by
        rw [h]
        exact Submodule.mem_top
      rw [Ideal.mem_quotient_iff_mem hIJ] at h1
      exact hJ.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
    · exact h
  haveI hmax : (x.map (Ideal.Quotient.mk p)).IsMaximal := mapmax p x ‹x.IsMaximal› hp
  have hmB : (maximalIdeal B).map (Ideal.Quotient.mk q) = maximalIdeal (B ⧸ q) :=
    IsLocalRing.eq_maximalIdeal (mapmax q _ (IsLocalRing.maximalIdeal.isMaximal B) hqm)
  have hcomap : (x.map (Ideal.Quotient.mk p)).comap (algebraMap (B ⧸ q) (C ⧸ p)) = maximalIdeal (B ⧸ q) := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.mem_comap, ← hmB, Ideal.mem_quotient_iff_mem hqm]
    change Ideal.Quotient.mk p (algebraMap B C b) ∈ _ ↔ _
    rw [Ideal.mem_quotient_iff_mem hp, ← Ideal.mem_comap, hx]
  refine ⟨t, ht, ?_⟩
  rw [UpperTheory.V.CA.localDimension_eq_height x p hp]
  exact g_dimform (B ⧸ q) (C ⧸ p) t hcm ht (x.map (Ideal.Quotient.mk p)) hcomap
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairKills
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

private theorem pk_starOp_single (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (a : R) :
    F.starOp O R n (MonoidAlgebra.single g a) =
      MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ (a * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R))) := by
  rw [GFrame.starOp, MonoidAlgebra.lift_single]
  show a • MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
  rw [← MulOpposite.op_smul, MonoidAlgebra.smul_single']

private theorem pk_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

private theorem eps_conj_eq_eps' (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε g
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, h]

private theorem star_star_monoidAlgebra (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (y : MonoidAlgebra R F.G₀) :
    F.star O R n (F.star O R n y) = y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [GFrame.star, map_add (f := _), MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    show MulOpposite.unop (F.starOp O R n (MulOpposite.unop (F.starOp O R n (MonoidAlgebra.single g a)))) =
      MonoidAlgebra.single g a
    rw [pk_starOp_single, MulOpposite.unop_op, pk_starOp_single, MulOpposite.unop_op]
    congr 1
    · rw [map_inv, inv_inv, pk_conj_conj]
    · rw [map_inv, eps_conj_eq_eps', inv_zpow, mul_assoc, Units.mul_inv, mul_one]

private theorem pk_surj (R : Type) [CommRing R] [Algebra O R] (n : ℕ) : Function.Surjective (F.starOp O R n) := by
  intro x
  refine ⟨F.star O R n (MulOpposite.unop x), ?_⟩
  apply MulOpposite.unop_injective
  exact star_star_monoidAlgebra F O R n (MulOpposite.unop x)

private theorem pk_eps (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (g : F.G₀) (m : ℤ) :
    algebraMap R B ((F.eps O R g ^ m : Rˣ) : R) = ((F.eps O B g ^ m : Bˣ) : B) := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, ← map_zpow, Units.coe_map, RingHom.coe_comp,
    Function.comp_apply, MonoidHom.coe_coe]
  exact (IsScalarTower.algebraMap_apply O R B _).symm

private theorem pk_bc (R B : Type) [CommRing R] [Algebra O R] [CommRing B] [Algebra R B] [Algebra O B]
    [IsScalarTower O R B] (n : ℕ) (y : MonoidAlgebra B F.G₀) :
    ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y))) = F.star O B n y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy =>
    simp only [map_add (f := _), GFrame.star, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]
  | single g b =>
    show _ = MulOpposite.unop (F.starOp O B n (MonoidAlgebra.single g b))
    rw [pk_starOp_single, MulOpposite.unop_op, toT_single, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      pk_starOp_single, one_mul, Det.unopS, LinearMap.baseChange_tmul]
    show ofT R F.G₀ B (b ⊗ₜ MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) = _
    have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B)
        (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) =
        MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap R B ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
      simp [MonoidAlgebra.mapRingHom]
    rw [ofT_tmul, hm, pk_eps, MonoidAlgebra.smul_single']

end

theorem UpperTheory.V.CA.pair_kills :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R), PhiCond (Γ := F.G₀) l → 1 ≤ n → F.IsPolar O p.D ∧ (∀ y, p.D.Kills y → p.D.Kills (F.star O R n y)) ∧ (∀ z ∈ TwoSidedIdeal.span p.D.CH, F.star O R n z ∈ TwoSidedIdeal.span p.D.CH) ∧ (∀ v g, p.D.Kills (F.oEl v (p.ψ v) g)) ∧ ∀ u, ∀ g ∈ r.Ip u, p.D.Kills (MonoidAlgebra.single g 1 - 1) := by
  intro l _ F O _ _ _ _ _ _ _ n r R _ _ _ p hphi hn
  have hspan : Submodule.span R (↑(MonoidHom.mrange (MonoidAlgebra.of R F.G₀)) : Set (MonoidAlgebra R F.G₀)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | single g a =>
      have hs : MonoidAlgebra.single g a = a • MonoidAlgebra.of R F.G₀ g := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
      rw [hs]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  have hlam : ∀ x ∈ MonoidHom.mrange (MonoidAlgebra.of R F.G₀), ∀ i : ℕ, 1 ≤ i → i ≤ n →
      p.D.toDet.lam i (MulOpposite.unop (F.starOp O R n x)) = p.D.toDet.lam i x := by
    rintro x ⟨g, rfl⟩ i _ _
    rw [(d_toDet p.D _).2.1, (d_toDet p.D _).2.1, MonoidAlgebra.of_apply]
    exact p.P i g
  obtain ⟨hpull, hCH, hker⟩ := d_star p.D.toDet (F.starOp O R n) _ hspan hlam
  have hpolar : F.IsPolar O p.D := by
    intro B _ _ _ _ y
    have h1 := congrArg (fun X : Det n R (MonoidAlgebra R F.G₀) => X.D B (toT R F.G₀ B y)) hpull
    change p.D.D B (ofT R F.G₀ B (Det.unopS R (MonoidAlgebra R F.G₀) B
      (Algebra.TensorProduct.map (AlgHom.id B B) (F.starOp O R n) (toT R F.G₀ B y)))) =
      p.D.D B (ofT R F.G₀ B (toT R F.G₀ B y)) at h1
    rw [pk_bc, ofT_toT] at h1
    exact h1
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have he : Function.Injective (ResidueField.map (algebraMap O R)) := (resMap_bijective O R).1
  haveI : Finite (ResidueField R) := Finite.of_surjective _ (resMap_bijective O R).2
  haveI : CharP (ResidueField R) l := charP_of_injective_ringHom he l
  let χ : Fin n → F.G₀ →* (ResidueField R)ˣ := fun i =>
    (Units.map (ResidueField.map (algebraMap O R) : ResidueField O →* ResidueField R)).comp (r.chib i)
  have hres : (ResidueField.map (algebraMap O R)).comp (res O R : R →+* ResidueField O) = residue R := by
    ext x
    show ResidueField.map (algebraMap O R) ((RingEquiv.ofBijective _ (resMap_bijective O R)).symm (residue R x)) =
      residue R x
    exact (RingEquiv.ofBijective _ (resMap_bijective O R)).apply_symm_apply _
  have hD : p.D.map (residue R) = GDet.ofChars χ := by
    rw [← hres, ← (d_gmap p.D).2.1, p.red, Resid.Dbar, (d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2, GDet.ofChars]
    congr 1
    ext g i j
    by_cases hij : i = j
    · subst hij
      simp [χ, diagRep, GDet.diagRep]
    · simp [χ, diagRep, GDet.diagRep, Matrix.diagonal_apply_ne _ hij]
  have hopen : ∀ i, IsOpen (↑(χ i).ker : Set F.G₀) := by
    intro i
    have hk : (χ i).ker = (r.chib i).ker := by
      ext g
      simp only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply]
      constructor
      · intro h
        apply Units.ext
        apply he
        have h2 := congrArg Units.val h
        simpa using h2
      · intro h
        rw [h, map_one]
    rw [hk]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    apply r.chib_inj
    ext g
    apply he
    have h2 := congrArg (fun f : F.G₀ →* (ResidueField R)ˣ => ((f g : (ResidueField R)ˣ) : ResidueField R))
      hij
    simpa [χ] using h2
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hphi hopen hinj
  have hK : ∀ y, p.D.Kills y ↔ ∀ g : F.G₀, p.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    fun y => g_kills_tr p.D χ p.cont hD hh hn y
  refine ⟨hpolar, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ p.D.toDet.ker := (d_ker p.D.toDet y).1.2 ((d_toDet p.D y).2.2.2.2 hy)
    exact (d_toDet p.D _).2.2.2.1 ((d_ker p.D.toDet _).1.1 (hker (pk_surj F O R n) y hy'))
  · intro z hz
    rw [← d_toDet_CH] at hz ⊢
    exact hCH z hz
  · intro v g
    exact (hK _).2 (p.Ord v g)
  · intro u g hg
    exact (hK _).2 (p.I u g hg)
end

