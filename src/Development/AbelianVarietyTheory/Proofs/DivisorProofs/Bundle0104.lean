module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEq
section
namespace GlobalTheory

theorem ringHom_extends_algHom_of_span_of_finrank_eq :
    ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A]
      [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B),
      Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O →
      ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  intro O _ _ _ A _ _ _ B _ _ φ ρ hspan hdim
  classical
  let b := Module.Free.chooseBasis ℤ O
  let v : Module.Free.ChooseBasisIndex ℤ O → A := fun i => φ (b i)
  have hle : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℂ A := by
    rw [hdim, Module.finrank_eq_card_chooseBasisIndex]
  let bA := basisOfTopLeSpanOfCardEqFinrank v hle hcard
  have hbA : ∀ i, bA i = φ (b i) := fun i => by
    simp only [bA, coe_basisOfTopLeSpanOfCardEqFinrank, v]
  let L : A →ₗ[ℂ] B := bA.constr ℂ (fun i => ρ (b i))
  have hLb : ∀ i, L (φ (b i)) = ρ (b i) := by
    intro i
    rw [← hbA]
    exact bA.constr_basis ℂ _ i
  have hLφ : ∀ x, L (φ x) = ρ x := by
    have h : (L.restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap
        = ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => hLb i)
    intro x
    exact LinearMap.congr_fun h x
  have hmul : ∀ u w : A, L (u * w) = L u * L w := by
    have h : (LinearMap.mul ℂ A).compr₂ L = (LinearMap.mul ℂ B).compl₁₂ L L := by
      refine bA.ext (fun i => bA.ext (fun j => ?_))
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', hbA]
      rw [← map_mul, hLφ, hLφ, hLφ, map_mul]
    intro u w
    exact LinearMap.congr_fun₂ h u w
  have hone : L 1 = 1 := by
    rw [← map_one φ, hLφ, map_one]
  exact ⟨AlgHom.ofLinearMap L hone hmul, fun x => by
    simp only [AlgHom.ofLinearMap_apply]; exact hLφ x⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreStalk

theorem fromSpecResidueField_eq {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by
  rw [← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]
  rfl

theorem image_eq (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by
  have := (π.range_fiberι b).le ⟨z, rfl⟩
  simpa using this

theorem ker_stalkMap_fiberι (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    RingHom.ker ((π.fiberι b).stalkMap z).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
        (π.stalkMap (π.fiberι b z)).hom := by
  have h' := image_eq B Y π b z
  have hA := fromSpecResidueField_eq h'
  apply le_antisymm
  · intro a ha
    let y := π.fiberι b z
    let S := Y.presheaf.stalk y
    let I := (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom
    have hIm : I ≤ IsLocalRing.maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (π.stalkMap y).hom r hr
    have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hIm)
    have : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let L : B.residueField (π y) ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom
      (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y)))
        ((Ideal.Quotient.mk I).comp (π.stalkMap y).hom)
        (fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)))
    have hres : B.residue (π y) ≫ L = π.stalkMap y ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext r; rfl
    let g : Spec (CommRingCat.of (S ⧸ I)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.fromSpecStalk y
    let t : Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (B.residueField b) := Spec.map ((B.residueFieldCongr h').inv ≫ L)
    have w : g ≫ π = t ≫ B.fromSpecResidueField b := by
      rw [hA, ← Category.assoc, ← Spec.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, g]
      rw [hres]
      first
        | (rw [Spec.map_comp (π.stalkMap y) (CommRingCat.ofHom (Ideal.Quotient.mk I)), Category.assoc,
            Scheme.SpecMap_stalkMap_fromSpecStalk])
        | (erw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])
      all_goals rfl
    let ℓ : Spec (CommRingCat.of (S ⧸ I)) ⟶ π.fiber b := Limits.pullback.lift g t w
    have hℓ : ℓ ≫ π.fiberι b = g := Limits.pullback.lift_fst _ _ _
    have e : ℓ (IsLocalRing.closedPoint _) = z := by
      apply (π.fiberι b).isEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
      exact (congrArg (Y.fromSpecStalk y) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := (π.fiber b).presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
    have hψ : (π.fiberι b).stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (Y.fromSpecStalk y)]
      change _ = g
      rw [← hℓ, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' := congrArg (fun q => q.hom a) hψ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
    rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
    exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm
  · obtain ⟨c, hc⟩ := Spec.map_surjective ((π.fiber b).fromSpecStalk z ≫ π.fiberToSpecResidueField b)
    have key : π.stalkMap (π.fiberι b z) ≫ (π.fiberι b).stalkMap z =
        B.residue _ ≫ (B.residueFieldCongr h').hom ≫ c := by
      apply Spec.map_injective
      rw [← cancel_mono (B.fromSpecStalk (π (π.fiberι b z)))]
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Scheme.Hom.fiber_fac, ← Category.assoc, ← hc, hA]
      simp only [Spec.map_comp, Category.assoc]
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun q => q.hom r) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have : (B.residue (π (π.fiberι b z))).hom r = 0 := (IsLocalRing.residue_eq_zero_iff r).2 hr
    rw [this, map_zero, map_zero]

theorem nonempty_ringEquiv_stalk_fiber (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    Nonempty ((Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) ≃+* (π.fiber b).presheaf.stalk z) := by
  rw [← ker_stalkMap_fiberι]
  exact ⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩

end GlobalTheory.FibreStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerate
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ringOfIntegers_trace_mulLeft_nondegenerate :
    ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K),
      (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro K _ _ x hx
  by_contra hne
  have hxK : (x : K) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_eq_zero_iff.mp h)
  have halg : IsAlgebraic ℤ ((x : K)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hdi⟩ := halg.exists_integral_multiple
  let y : 𝓞 K := ⟨d • (x : K)⁻¹, hdi⟩
  have hxy : x * y = algebraMap ℤ (𝓞 K) d := by
    apply RingOfIntegers.coe_injective
    show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)
    rw [eq_intCast, zsmul_eq_mul]
    push_cast
    field_simp
    first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp
  have h := hx y
  rw [hxy] at h
  have h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d))
      = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d) := by
    rw [Algebra.trace_apply]; rfl
  rw [h2, Algebra.trace_algebraMap] at h
  have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) hpos.ne'
  · exact hd0 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootModelPointHeightDegree
section
namespace GlobalTheory.ClassPart

private lemma summand_conj {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (η : Γ) (y : Y) (γ : Γ) :
    ((Nat.card (MulAction.stabilizer Γ (η • y) ⊓ Subgroup.centralizer {η * γ * η⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (η • y) (η * γ * η⁻¹) =
      ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y γ := by
  rw [hF]
  congr 3
  symm
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_
  intro s
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  refine and_congr_right (fun _ => ?_)
  change s * γ = γ * s ↔ (η * s * η⁻¹) * (η * γ * η⁻¹) = (η * γ * η⁻¹) * (η * s * η⁻¹)
  rw [show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group,
    show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]

theorem orbitSum_conj : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  intro Γ Y _ _ F hF γ g
  set S : Γ → Y → ℂ := fun c y =>
    ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef
  have hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y := fun η y c => summand_conj F hF η y c
  have hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y := by
    intro c ζ hζ y
    have hcj : ζ * c * ζ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hζ
      rw [hζ]; group
    have := hS ζ y c
    rwa [hcj] at this
  set γ' := g * γ * g⁻¹ with hγ'
  have hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔
      (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]
    constructor
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g * ζ * g⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ']
        change (g * ζ * g⁻¹) * (g * γ * g⁻¹) = (g * γ * g⁻¹) * (g * ζ * g⁻¹)
        rw [show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group,
          show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]
      · rw [← h]; simp [mul_smul]
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g⁻¹ * ζ * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ'] at hζ
        have h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g := by rw [hζ]
        rw [show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group,
          show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group] at h2
        exact h2.symm
      · have := congrArg (g⁻¹ • ·) h
        simpa [mul_smul] using this
  let e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃
      MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y :=
    Quotient.congr (MulAction.toPerm g) hrel
  change ∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro o
  have hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) =
      Quotient.mk _ (g • Quotient.out o) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hr := Quotient.exact hmk
  have hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o) := hr
  rw [MulAction.mem_orbit_iff] at hr'
  obtain ⟨ζ, hζ⟩ := hr'
  rw [← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]

end GlobalTheory.ClassPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
section
noncomputable section

namespace GlobalTheory.StdLoc

def rowBlockIndicatorFrom (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

def blockPar (R : Type) [CommRing R] (a d : ℕ) : Subgroup (GL (Fin d) R) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)}
  mul_mem' := fun {x y} hx hy => by
    show ((x * y : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_mul]; exact hx.mul hy
  one_mem' := by
    show ((1 : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_one]; exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    show ((x⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    letI : Invertible (x : Matrix (Fin d) (Fin d) R) := Units.invertible x
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem _root_.GlobalTheory.StdLoc.mem_blockPar {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by
  show (g : Matrix (Fin d) (Fin d) R).BlockTriangular (_root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom a) ↔ _
  unfold Matrix.BlockTriangular _root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom
  constructor
  · intro h i j hj hi
    apply h
    simp [hi, not_le.mpr hj]
  · intro h i j hlt
    refine h i j ?_ ?_ <;> split_ifs at hlt <;> omega

def glVol (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)

def blockIdx (q : ℝ) (c a a' : ℕ) : ℝ := q ^ (c * a * a') * glVol q (a + a') / (glVol q a * glVol q a')

end GlobalTheory.StdLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
section
namespace GlobalTheory.AdTh

theorem scalar_of_intertwines_up_to_scalar (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] [Nontrivial M] (ρ : Γ →* Module.End ℂ M) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (htr : ∀ γ ∈ S, LinearMap.trace ℂ M (ρ γ) ≠ 0)
    (hirr : ∀ U : Submodule ℂ M, (∀ γ, U.map (ρ γ) ≤ U) → U = ⊥ ∨ U = ⊤)
    (T : M →ₗ[ℂ] M) (χ : Γ → ℂ) (hT : Function.Injective T)
    (h : ∀ γ x, T (ρ γ x) = χ γ • ρ γ (T x)) : ∃ a : ℂ, ∀ x, T x = a • x := by
  have hu : IsUnit (T : Module.End ℂ M) :=
    (Module.End.isUnit_iff _).2 ⟨hT, LinearMap.injective_iff_surjective.1 hT⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ∀ γ, (u : Module.End ℂ M) * ρ γ = χ γ • (ρ γ * u) := by
    intro γ
    ext x
    simp [hu, h]
  have hχ : ∀ γ ∈ S, χ γ = 1 := by
    intro γ hγ
    have h2 : (u : Module.End ℂ M) * ρ γ * (↑u⁻¹ : Module.End ℂ M) = χ γ • ρ γ := by
      rw [h1, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    have h3 := congrArg (LinearMap.trace ℂ M) h2
    rw [LinearMap.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul, map_smul, smul_eq_mul] at h3
    have h4 := htr γ hγ
    have : (χ γ - 1) * LinearMap.trace ℂ M (ρ γ) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd h5 h4
  have hc : ∀ γ, Commute (u : Module.End ℂ M) (ρ γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      have := h1 x
      rw [hχ x hx, one_smul] at this
      exact this
    | one => rw [map_one]; exact Commute.one_right _
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_right hy
    | inv x _ hx =>
      have e1 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact Commute.units_inv_right (u := ⟨ρ x, ρ x⁻¹, e1, e2⟩) hx
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ M)
  refine ⟨a, fun x => ?_⟩
  rcases hirr (Module.End.eigenspace T a) (by
      rintro γ _ ⟨y, hy, rfl⟩
      have hy' : T y = a • y := Module.End.mem_eigenspace_iff.1 hy
      rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f : Module.End ℂ M => f y) (hc γ).eq
      simp only [hu, Module.End.mul_apply] at this
      rw [this, hy', map_smul]) with h0 | h0
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 ha)
  · exact Module.End.mem_eigenspace_iff.1 (h0 ▸ Submodule.mem_top)

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeHomExtOfJointlyInjective
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem scheme_hom_ext_of_jointly_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  intro Z Z₁ Z₂ X e₁ e₂ hcov hinj f g h₁ h₂
  have hbase : f.base = g.base := by
    ext z
    rcases hcov z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
    · have := congrArg (fun k : Z₁ ⟶ X => k z₁) h₁
      simpa [Scheme.Hom.comp_apply] using this
    · have := congrArg (fun k : Z₂ ⟶ X => k z₂) h₂
      simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ {Y : Scheme.{0}} (e : Y ⟶ Z), e ≫ f = e ≫ g → ∀ U : X.Opens,
      (f.app U ≫ Z.presheaf.map (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj U)).op) ≫
        e.app (g ⁻¹ᵁ U) = g.app U ≫ e.app (g ⁻¹ᵁ U) := by
    intro Y e he U
    rw [Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app,
      Scheme.Hom.congr_app he]
    simp [Scheme.Hom.comp_app]
    conv_rhs => rw [← Category.comp_id (Scheme.Hom.app e (g ⁻¹ᵁ U))]
    congr 2
    exact (Y.presheaf.map_comp _ _).symm.trans
      ((congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _))
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  apply hinj (g ⁻¹ᵁ U)
  · exact congr(($(key e₁ h₁ U)).hom s)
  · exact congr(($(key e₂ h₂ U)).hom s)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjective
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine
    (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens)
    (h : ∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) :
    IsSchemeTheoreticallyDominant W.ι := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := X.isBasis_affineOpens.isOpenCover_mem_and_le
    (T.isBasis_affineOpens.isOpenCover.comap p.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨U, ⟨V, hV⟩⟩, hU, hUV : U ≤ p ⁻¹ᵁ V⟩
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro b hb
  have hb' : W.ι.app U b = 0 := W.ι.ideal_ker_le ⟨U, hU⟩ hb
  refine h U V hU hV hUV b fun x hx hxW ↦ ?_
  have h1 := Scheme.Hom.germ_stalkMap_apply W.ι U ⟨x, hxW⟩ hx b
  rw [hb', map_zero] at h1
  let y : W.toScheme := ⟨x, hxW⟩
  have hiso : IsIso (W.ι.stalkMap y) := inferInstance
  have hinj : Function.Injective (W.ι.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  exact hinj (h1.trans (map_zero _).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierRepresentation
section
open MeasureTheory

namespace GlobalTheory


open Real in
theorem schwartz_eq_fourier_synthesis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  intro V _ _ _ m
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm m
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ ξ x, A ξ x = 2 * π * inner ℝ ξ (e x) := by
    intro ξ x
    simp [A]
  refine ⟨Module.finrank ℝ V, A, (FourierTransform.fourier m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ), fun x => ?_⟩
  have h1 : m x = m' (e x) := by
    simp [m']
  have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x)) (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) m')
  rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  ext ξ
  rw [hA, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory
end

