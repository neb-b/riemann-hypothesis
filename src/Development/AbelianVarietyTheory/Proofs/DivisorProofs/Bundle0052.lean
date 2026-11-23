module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeToNumberField
section
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  haveI : CharZero (R ⧸ m) := algebraRat.charZero _
  have hfin := (inferInstance : Module.Finite ℚ (R ⧸ m))
  haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by
    have e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    convert hfin
    first
      | exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm
      | (rw [← e]; rfl)
  haveI : NumberField (R ⧸ m) := ⟨⟩
  exact ⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩

theorem exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  intro A _ _ _ hA a ha
  classical
  obtain ⟨s, hs⟩ := hA.out
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let B : Subalgebra ℚ F := Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))
  have hmem : ∀ x : A, f x ∈ B := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap n =>
      have : f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ) := by simp [f]
      rw [this]; exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  have hinv : (f a)⁻¹ ∈ B := Algebra.subset_adjoin (Set.mem_insert _ _)
  haveI hBft : Algebra.FiniteType ℚ B := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩
  have hfa : f a ≠ 0 := by
    simpa [f] using (IsFractionRing.injective A F).ne ha
  let ψ : A →+* B := f.codRestrict B hmem
  have hu : IsUnit (ψ a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩
    show f a * (f a)⁻¹ = 1
    exact mul_inv_cancel₀ hfa
  obtain ⟨K, _, _, φ, -⟩ := exists_numberField_of_finiteType_rat B
  exact ⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange
section
open TensorProduct

namespace GlobalTheory.DualFibreRank

section
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]

noncomputable def cmp (M : Type) [AddCommGroup M] [Module O M] :
    A ⊗[O] Module.Dual O M →ₗ[A] Module.Dual A (A ⊗[O] M) :=
  LinearMap.liftBaseChange A (Module.Dual.baseChange A)

variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

theorem cmp_natural (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by
  ext g x
  simp [cmp]

theorem cmp_natural_apply (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) :=
  LinearMap.congr_fun (cmp_natural A f) x

theorem cmp_bijective_of_free [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  have h := (TensorProduct.isBaseChange O M A)
  have : cmp A M (O := O) = h.toDualBaseChange.toLinearMap := by
    ext g x
    have := h.toDualBaseChange_tmul 1 g x
    simp only [TensorProduct.mk_apply] at this
    simp [cmp, this, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact h.toDualBaseChange.bijective

theorem cmp_bijective [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  have hF := cmp_bijective_of_free A (O := O) (M := Fin n → O)
  have h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  have h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]
    simp [LinearMap.dualMap_id]
  constructor
  · intro x y hxy
    rw [← h1 x, ← h1 y]
    congr 1
    apply hF.1
    rw [cmp_natural_apply, cmp_natural_apply, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hF.2 ((p.baseChange A).dualMap y)
    exact ⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩

end

theorem finrank_dual_and_range_dualMap_baseChange :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by
  intro O M N κ _ _ _ _ _ _ _ _ _ _ _ f
  let eM := LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)
  refine ⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ),
    ← LinearEquiv.finrank_map_eq eM]
  have : (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) =
      LinearMap.range (f.baseChange κ).dualMap := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _
    rw [cmp_natural, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (cmp_bijective κ).2
  rw [this]

end GlobalTheory.DualFibreRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrix
section
open NumberField

namespace GlobalTheory

theorem finrank_dvd_of_ringOfIntegers_to_matrix (E : Type) [Field E] [NumberField E] {r : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  let g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ := (Int.castRingHom ℚ).mapMatrix.comp ρ
  let S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ) := Algebra.adjoin ℚ (Set.range g)
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    change g a * g b = g b * g a
    rw [← map_mul, mul_comm, map_mul])
  open scoped IsMulCommutative in
  letI : CommRing S := inferInstance
  let g₁ : 𝓞 E →+* S := g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  have hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y) := by
    rintro ⟨_, m, hm, rfl⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm
    have : g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ) := by
      apply Subtype.ext
      simp [g₁, g, map_intCast]
    rw [this]
    exact (IsUnit.mk0 _ hm0).map _
  let ρ' : E →+* Matrix (Fin r) (Fin r) ℚ := S.val.toRingHom.comp (IsLocalization.lift hg)
  letI : Module E (Fin r → ℚ) :=
    Module.compHom (Fin r → ℚ)
      ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')
  have hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ) := RingHom.ext_rat _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := by
    refine ⟨fun q e v => ?_⟩
    show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul]
    rfl
  refine ⟨Module.finrank E (Fin r → ℚ), ?_⟩
  have := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
  rw [Module.finrank_fin_fun] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.FinrankComp

theorem finrank_eq_mul_of_rankAtStalk (K S T : Type*) [Field K] [CommRing S] [AddCommGroup T]
    [Algebra K S] [Module S T] [Module K T] [IsScalarTower K S T] [Module.Finite K S]
    [Module.Finite S T] [Module.Flat S T] (d : ℕ)
    (h : ∀ p : PrimeSpectrum S, Module.rankAtStalk T p = d) :
    Module.finrank K T = d * Module.finrank K S := by
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq S T d
    (fun P => by
      have := P.isMaximal
      letI := Ideal.Quotient.field P.asIdeal
      have h1 := Module.rankAtStalk_baseChange (R := S) (M := T) (S := S ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, h] at h1
      exact h1)
  rw [(b.equivFun.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_comp_field {X Y : Scheme.{0}} (K : CommRingCat.{0}) (hK : IsField K)
    (φ : X ⟶ Y) (ψ : Y ⟶ Spec K) [IsFinite φ] [Flat φ] [IsFinite ψ] [Flat ψ] (d : ℕ)
    (h : ∀ y, φ.finrank y = d) (z : Spec K) : (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · have _ : IsAffine Y := isAffine_of_isAffineHom ψ
    have := this (φ ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ ψ) (fun y => by
      rw [← h (Y.isoSpec.inv y)]
      exact Scheme.Hom.finrank_of_isPullback (𝟙 X) _ φ Y.isoSpec.inv
        (IsPullback.of_horiz_isIso ⟨by simp⟩) y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom φ
    have := this (X.isoSpec.inv ≫ φ) (fun y => by simpa using h y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective ψ
  obtain ⟨g, rfl⟩ := Spec.map_surjective φ
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rename_i hf1 hf2 hg1 hg2
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank (f := f ≫ g) (hg1.comp hf1) (hf2.comp hg2),
    Scheme.Hom.finrank_SpecMap_eq_finrank hf1 hf2]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hg1 hg2] at h
  letI := hK.toField
  algebraize [f.hom, g.hom, (f ≫ g).hom]
  rw [← RingHom.algebraMap_toAlgebra g.hom, RingHom.finrank_algebraMap] at h
  rw [← RingHom.algebraMap_toAlgebra f.hom, ← RingHom.algebraMap_toAlgebra (f ≫ g).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  have : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq' rfl
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk K S T d h

theorem finrank_comp_of_const {X Y Z : Scheme.{0}} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsFinite φ] [Flat φ]
    [IsFinite ψ] [Flat ψ] (d : ℕ) (h : ∀ y, φ.finrank y = d) (z : Z) :
    (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  let i := Z.fromSpecResidueField z
  let pt : Spec (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  have hz : i pt = z := Scheme.fromSpecResidueField_apply z pt
  have hp := (IsPullback.of_hasPullback φ (pullback.fst ψ i)).paste_vert
    (IsPullback.of_hasPullback ψ i)
  rw [← hz, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp pt,
    ← Scheme.Hom.finrank_pullback_snd ψ i pt]
  exact finrank_comp_field _ (Field.toIsField _) _ _ d
    (fun y => by rw [Scheme.Hom.finrank_pullback_snd, h]) pt

end GlobalTheory.FinrankComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqZeroOfDualKilledByTensor
section
open NumberField Polynomial

namespace GlobalTheory

theorem ringOfIntegers_action_injective (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Nontrivial X] (ρ : 𝓞 F →+* Module.End ℤ X) :
    Function.Injective ρ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ RingHom.ker ρ := ha
  have hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ := Ideal.absNorm_mem _
  rw [RingHom.mem_ker, map_natCast] at hn
  obtain ⟨χ, hχ⟩ := exists_ne (0 : X)
  have h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0 := by
    have := congrArg (fun f : Module.End ℤ X => f χ) hn
    simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℤ] at h1
  have h2 : Ideal.absNorm (RingHom.ker ρ) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hχ
  rw [Ideal.absNorm_eq_zero_iff] at h2
  rw [h2] at hmem
  simpa using hmem

theorem dvd_coord_of_action_dvd (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Nontrivial X]
    (ρ : 𝓞 F →+* Module.End ℤ X) (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F))
    (p : ℤ) (hp : p ≠ 0) (a : 𝓞 F)
    (h : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      p ∣ (Module.Free.chooseBasis ℤ X).repr (ρ a χ) r) :
    ∀ i, p ∣ b.repr a i := by
  set B := Module.Free.chooseBasis ℤ X
  let T : Module.End ℤ X := B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)
  have hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a := by
    apply B.ext
    intro s
    rw [Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]
    conv_rhs => rw [← B.sum_repr (ρ a (B s))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.mul_ediv_cancel' (h _ r)]
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) T
  have hf' : aeval T f = 0 := by rw [aeval_def]; exact hf
  have h1 := Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'
  rw [hT] at h1
  have h2 : aeval a (f.scaleRoots p) = 0 := by
    apply ringOfIntegers_action_injective F X ρ
    rw [map_zero]
    have := Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)
    change ρ.toIntAlgHom _ = 0
    rw [← this]
    exact h1
  have h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, h2, map_zero]
  have hpF : (algebraMap ℤ F p) ≠ 0 := by simpa using hp
  set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef
  have hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a := by
    rw [hβdef]; field_simp
  have h4 : eval₂ (algebraMap ℤ F) β f = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p
    rw [hβa, ← aeval_def, h3] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)
  have hβ : IsIntegral ℤ β := ⟨f, hfm, h4⟩
  let y : 𝓞 F := ⟨β, hβ⟩
  have hy : p • y = a := by
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, zsmul_eq_mul]
    have : algebraMap (𝓞 F) F y = β := rfl
    rw [this, ← hβa]
    simp
  intro i
  refine ⟨b.repr y i, ?_⟩
  rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem finrank_eq_zero_of_dual_killed : ∀ (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X)
    (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k),
    w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) →
    Module.finrank ℤ X = 0 := by
  intro F _ _ X _ _ _ ρ k _ ι _ b w hw hyp
  classical
  by_contra hX
  haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)
  set B := Module.Free.chooseBasis ℤ X
  have key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0 := by
    intro χ r
    have := hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_comm]
  have lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r := by
    intro e χ r
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · set p := ringChar k with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP k p := ringChar.charP k
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)
    set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef
    have hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r := by
      intro χ r
      rw [lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := congrArg π (key χ r)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      rw [← this]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hedef]
      simp [ZMod.natCast_zmod_val, mul_comm]
    have h := GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0
    rw [Module.Basis.repr_sum_self] at h
    apply hπ
    rw [← ZMod.natCast_zmod_val (π (w i0))]
    have h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact_mod_cast h'
  · haveI : CharZero k := by
      have := ringChar.charP k; rw [hp] at this; exact CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)
    set c : ι → ℚ := fun i => π (w i) with hcdef
    set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef
    have he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]
      push_cast; rfl
    have hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        B.repr (ρ (∑ i, e i • b i) χ) r = 0 := by
      intro χ r
      rw [lin]
      have := congrArg π (key χ r)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      simp only [map_zsmul] at this
      have h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ)
          = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [he, zsmul_eq_mul, hcdef]; ring
      rw [this, mul_zero] at h2
      exact_mod_cast h2
    have hρ : ρ (∑ i, e i • b i) = 0 := by
      ext χ
      simp only [LinearMap.zero_apply]
      exact B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]
    have ha : (∑ i, e i • b i) = 0 :=
      GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])
    have h0 := congrArg (fun x => b.repr x i0) ha
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0
    have hc0 : c i0 ≠ 0 := hπ
    have : (e i0 : ℚ) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)
    exact this (by exact_mod_cast h0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMul
section
open NumberField

namespace GlobalTheory

open TensorProduct nonZeroDivisors in
theorem finrank_int_eq_finrank_ringOfIntegers_mul : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  intro E _ _ N _ _ _ _
  let g : N →ₗ[𝓞 E] E ⊗[𝓞 E] N := TensorProduct.mk (𝓞 E) E N 1
  have hb : IsBaseChange E g := TensorProduct.isBaseChange (𝓞 E) N E
  have h1 : Module.finrank E (E ⊗[𝓞 E] N) = Module.finrank (𝓞 E) N := hb.finrank_eq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E := inferInstance
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) g :=
    (isLocalizedModule_iff_isBaseChange _ E g).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (g.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars ℤ⁰ g
  have h4 : Module.finrank ℤ (E ⊗[𝓞 E] N) = Module.finrank ℤ N :=
    IsLocalizedModule.finrank_eq ℤ⁰ (g.restrictScalars ℤ) le_rfl
  have h5 : Module.finrank ℚ (E ⊗[𝓞 E] N) = Module.finrank ℤ (E ⊗[𝓞 E] N) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  rw [← h4, ← h5, ← h1, mul_comm, Module.finrank_mul_finrank]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaDegBotEqFinrankFiniteDomain
section
namespace GlobalTheory

theorem inertiaDeg_bot_eq_finrank : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  intro R S _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  haveI : (⊥ : Ideal S).LiesOver (⊥ : Ideal R) :=
    ⟨(Ideal.comap_bot_of_injective (algebraMap R S) hinj).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  rw [Ideal.inertiaDeg_eq (⊥ : Ideal R) (⊥ : Ideal S)]
  exact IsFractionRing.finrank_eq R (⊥ : Ideal R).ResidueField S
    (⊥ : Ideal S).ResidueField

end GlobalTheory
end

