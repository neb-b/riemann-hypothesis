module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChange
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing

namespace GlobalTheory

theorem specializes_lift_closedFibre_stalkBaseChange : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  intro X Y π z R _ _ i _ hi v y hv hsp hy
  let e : IsLocalRing.ResidueField (Y.presheaf.stalk z) ≃+* IsLocalRing.ResidueField R :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map i) ⟨(IsLocalRing.ResidueField.map i).injective, hi⟩
  let β : R →+* IsLocalRing.ResidueField (Y.presheaf.stalk z) := e.symm.toRingHom.comp (IsLocalRing.residue R)
  have hβ : β.comp i = IsLocalRing.residue _ := by
    ext x
    simp only [β, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← IsLocalRing.ResidueField.map_residue]
    exact e.symm_apply_apply (IsLocalRing.residue _ x)
  have hcomp : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) ≫ Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z = Y.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hβ]
    rfl
  have hβcl : Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z) (IsLocalRing.closedPoint (Y.residueField z)) = IsLocalRing.closedPoint R := by
    have : IsLocalHom β := inferInstance
    exact IsLocalRing.comap_closedPoint β
  let g : π.fiber z ⟶ pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π :=
    pullback.lift (π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (π.fiberι z)
      (by rw [Category.assoc]; exact (congrArg (π.fiberToSpecResidueField z ≫ ·) hcomp).trans (π.fiber_fac z).symm)
  have hgq : g ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberι z := pullback.lift_snd _ _ _
  let h : pullback (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ⟶ π.fiber z :=
    pullback.lift (pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) (pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π))
      (by
        rw [Category.assoc, ← pullback.condition (f := (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z)) (g := π), ← Category.assoc,
          ← pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), Category.assoc]; exact congrArg _ hcomp)
  have hgf : g ≫ pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π = π.fiberToSpecResidueField z ≫ (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) := pullback.lift_fst _ _ _
  have hhf : h ≫ π.fiberToSpecResidueField z = pullback.fst (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := pullback.lift_snd _ _ _
  have hhι : h ≫ π.fiberι z = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) ≫ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π := pullback.lift_fst _ _ _
  have hhg : h ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z)) (pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, ← Category.assoc, hhf]
      exact pullback.condition (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    · rw [Category.assoc, hgq, hhι]
  obtain ⟨u, -, hu2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Spec.map (CommRingCat.ofHom β : CommRingCat.of R ⟶ Y.residueField z))) (g := pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)
    (IsLocalRing.closedPoint (Y.residueField z)) v (hβcl.trans hv.symm)
  have hga : g (h u) = v := by
    rw [← Scheme.Hom.comp_apply, hhg, hu2]
  have hfa : π.fiberι z (h u) = pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v := by
    rw [← hga, ← Scheme.Hom.comp_apply g, hgq]
  let b := (π.fiberHomeo z).symm ⟨y, hy⟩
  have hb : π.fiberι z b = y := π.fiberι_fiberHomeo_symm z ⟨y, hy⟩
  have hab : h u ⤳ b := by
    rw [← (π.fiberι z).isEmbedding.toIsInducing.specializes_iff, hfa, hb]
    exact hsp
  refine ⟨g b, ?_, ?_⟩
  · rw [← hga]
    exact hab.map g.continuous
  · rw [← Scheme.Hom.comp_apply, hgq, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqId
section
namespace GlobalTheory.SquareDistanceExpansion

open Matrix

theorem expand {R : Type} [CommRing R] {n : ℕ} (X Y X' Y' : Matrix (Fin n) (Fin n) R) :
    (1 + X + Y) * (1 + X' + Y') = 1 + X + Y + X' + Y' + X * X' + X * Y' + Y * X' + Y * Y' := by
  noncomm_ring

theorem sq_id {R : Type} [CommRing R] {d : ℕ} (H H' : Matrix (Fin d) (Fin d) R) :
    H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by
  noncomm_ring

theorem prod_eq {R : Type} [CommRing R] {n d : ℕ} (a c : Matrix (Fin n) (Fin d) R)
    (α γ : Matrix (Fin d) (Fin n) R) (M N : Matrix (Fin d) (Fin d) R) :
    a * M * α * (c * N * γ) = a * M * (α * c) * N * γ := by
  simp only [Matrix.mul_assoc]

theorem dist {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem main : (let d1 : {R : Type} → [CommRing R] → {n d : ℕ} → Matrix (Fin n) (Fin d) R → Matrix (Fin n) (Fin d) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin d) R → Matrix (Fin d) (Fin d) R → Matrix (Fin n) (Fin n) R := @(fun {R : Type} [CommRing R] {n d : ℕ} (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) ↦ (1 : Matrix (Fin n) (Fin n) R) + a * (H - (1 : Matrix (Fin d) (Fin d) R)) * α + b * (K - (1 : Matrix (Fin d) (Fin d) R)) * β); ∀ {R : Type} [inst : CommRing R] {n d : ℕ} {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}, α * a = (1 : Matrix (Fin d) (Fin d) R) → β * b = (1 : Matrix (Fin d) (Fin d) R) → α * b = (0 : Matrix (Fin d) (Fin d) R) → β * a = (0 : Matrix (Fin d) (Fin d) R) → ∀ (H K H' K' : Matrix (Fin d) (Fin d) R), d1 a b α β H K * d1 a b α β H' K' = d1 a b α β (H * H') (K * K')) := by
  dsimp only
  intro R _ n d a b α β hαa hβb hαb hβa H K H' K'
  have e1 := prod_eq a a α α (H - 1) (H' - 1)
  have e2 := prod_eq a b α β (H - 1) (K' - 1)
  have e3 := prod_eq b a β α (K - 1) (H' - 1)
  have e4 := prod_eq b b β β (K - 1) (K' - 1)
  rw [hαa, Matrix.mul_one] at e1
  rw [hαb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e2
  rw [hβa, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e3
  rw [hβb, Matrix.mul_one] at e4
  rw [expand, e1, e2, e3, e4, sq_id H H', sq_id K K', dist a α (H - 1) (H' - 1),
    dist b β (K - 1) (K' - 1)]
  abel

end GlobalTheory.SquareDistanceExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqScalarCharacterOfDoubleCoverUnitary
section
open scoped Matrix

namespace GlobalTheory

theorem sq_scalar_character : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  intro G G' M H _ _ _ _ _ _ _ _ _ pr s om ω ε hcov hsurj hker hε hs hom hω hrel
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  have huniq : ∀ g (g₁ g₂ : G') (a b : ℂ), pr g₁ = s g → pr g₂ = s g →
      (∀ v, ω g v = a • om g₁ v) → (∀ v, ω g v = b • om g₂ v) → a ^ 2 = b ^ 2 := by
    intro g g₁ g₂ a b h₁ h₂ ha hb
    have hw : om g₁ v₀ ≠ 0 := by
      intro h; apply hv₀; exact (om g₁).map_eq_zero_iff.mp h
    have hk : pr (g₁⁻¹ * g₂) = 1 := by simp [map_mul, map_inv, h₁, h₂]
    rcases hker _ hk with h | h
    · have h2 : g₂ = g₁ := by rw [← mul_inv_cancel_left g₁ g₂, h, mul_one]
      subst h2
      have : a • om g₂ v₀ = b • om g₂ v₀ := by rw [← ha, ← hb]
      have hab : a = b := smul_left_injective ℂ hw this
      rw [hab]
    · have h2 : g₂ = g₁ * ε := by rw [← h, mul_inv_cancel_left]
      have : a • om g₁ v₀ = (-b) • om g₁ v₀ := by
        rw [← ha, hb, h2, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hε,
          map_neg, smul_neg, neg_smul]
      have hab : a = -b := smul_left_injective ℂ hw this
      rw [hab]; ring
  have hlift : ∀ g, ∃ g', pr g' = s g := fun g => hsurj (s g)
  choose L hL using hlift
  choose A hA using fun g => hrel g (L g) (hL g)
  refine ⟨fun g => A g ^ 2, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmul : pr (L g * L h) = s (g * h) := by simp [map_mul, hL]
    have hsc : ∀ v, ω (g * h) v = (A g * A h) • om (L g * L h) v := by
      intro v
      rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hA h, LinearIsometryEquiv.map_smul,
        hA g, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, smul_smul, mul_comm (A h)]
    have := huniq (g * h) (L (g * h)) (L g * L h) _ _ (hL _) hmul (hA _) hsc
    simp only
    rw [this]; ring
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨e, he, hpe⟩ := hcov.isLocalHomeomorph (L g₀)
    have hopen : IsOpen (s ⁻¹' e.target) := e.open_target.preimage hs
    have hmem : g₀ ∈ s ⁻¹' e.target := by
      show s g₀ ∈ e.target
      rw [← hL g₀, hpe]; exact e.map_source he
    let f : G → ℂ := fun g => (inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀) ^ 2
    have hf : ContinuousAt f g₀ := by
      have h1 : ContinuousAt (fun g => om (e.symm (s g)) v₀) g₀ :=
        (hom v₀).continuousAt.comp ((e.continuousAt_symm hmem).comp hs.continuousAt)
      exact ((h1.inner (hω v₀).continuousAt).div_const _).pow 2
    refine hf.congr ?_
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hpr : pr (e.symm (s g)) = s g := by rw [hpe]; exact e.right_inv hg
    obtain ⟨c, hc⟩ := hrel g _ hpr
    have hcval : c = inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀ := by
      rw [hc, inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_assoc,
        div_self (inner_self_ne_zero.2 hv₀), mul_one]
    show f g = A g ^ 2
    simp only [f]
    rw [← hcval]
    exact huniq g _ _ c (A g) hpr (hL g) hc (hA g)
  · intro g
    refine pow_ne_zero 2 ?_
    intro h0
    have := hA g v₀
    rw [h0, zero_smul] at this
    exact hv₀ ((ω g).map_eq_zero_iff.mp this)
  · intro g g' a hg' ha
    exact huniq g g' (L g) a (A g) hg' (hL g) ha (hA g)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroDeformationFactorsThroughLinear
section
namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

variable {R₀ B K : Type} [CommRing R₀] [CommRing B] [Field K] [Algebra R₀ B]
  [Algebra B K] [Algebra R₀ K] [IsScalarTower R₀ B K]

def derOf (h : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0) : Derivation R₀ B K :=
  Derivation.mk'
    { toFun := fun b => (h b).snd
      map_add' := fun x y => by simp
      map_smul' := fun a b => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, snd_mul, hc, hfst, smul_zero, add_zero, smul_eq_mul,
          ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, snd_mul, hfst, Algebra.smul_def,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, Algebra.algebraMap_self,
        RingHom.id_apply]
      ring)

lemma derOf_injective (h h' : B →+* DualNumber K) (hfst : ∀ b, (h b).fst = algebraMap B K b)
    (hc : ∀ a : R₀, (h (algebraMap R₀ B a)).snd = 0)
    (hfst' : ∀ b, (h' b).fst = algebraMap B K b)
    (hc' : ∀ a : R₀, (h' (algebraMap R₀ B a)).snd = 0)
    (e : derOf h hfst hc = derOf h' hfst' hc') : h = h' := by
  ext b
  · rw [hfst, hfst']
  · have := congrArg (fun D : Derivation R₀ B K => D b) e
    simpa [derOf] using this

lemma derivation_eq_of_basis {ι : Type} (e : Module.Basis ι B Ω[B⁄R₀]) (D D' : Derivation R₀ B K)
    (h : ∀ j, D.liftKaehlerDifferential (e j) = D'.liftKaehlerDifferential (e j)) : D = D' := by
  have : D.liftKaehlerDifferential = D'.liftKaehlerDifferential := e.ext h
  rw [← Derivation.liftKaehlerDifferential_comp D, ← Derivation.liftKaehlerDifferential_comp D', this]

lemma liftKaehler_eq_sum {ι : Type} [Fintype ι] (D : Derivation R₀ B K) (Ds : ι → Derivation R₀ B K)
    (c : ι → K) (h : ∀ x, D x = ∑ i, c i * Ds i x) (ω : Ω[B⁄R₀]) :
    D.liftKaehlerDifferential ω = ∑ i, c i * (Ds i).liftKaehlerDifferential ω := by
  let φ : Ω[B⁄R₀] →ₗ[B] K :=
    { toFun := fun ω => ∑ i, c i * (Ds i).liftKaehlerDifferential ω
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun b x => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have : D.liftKaehlerDifferential = φ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [φ, Derivation.liftKaehlerDifferential_comp_D, h]
  rw [this]; rfl

end FirstOrderPoints

end GlobalTheory

namespace GlobalTheory

namespace FirstOrderPoints

open TrivSqZeroExt

theorem exists_linearCombination_eq :
    ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  intro R₀ B K _ _ _ _ n hsm ι _ hcard R hR hinj g hgfst hg
  classical
  haveI : Algebra.IsStandardSmooth R₀ B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let ρ : B →+* K := (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R
  letI : Algebra B K := ρ.toAlgebra
  letI : Algebra R₀ K := (ρ.comp (algebraMap R₀ B)).toAlgebra
  haveI : IsScalarTower R₀ B K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := ρ.domain_nontrivial
  have hfin : Module.finrank B Ω[B⁄R₀] = n := by
    have := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R₀) (S := B) n
    rw [← Module.finrank_eq_rank] at this
    exact_mod_cast this
  let e := Module.finBasisOfFinrankEq B Ω[B⁄R₀] hfin
  let hM : (ι → K) → B →+* DualNumber K := fun M =>
    (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R
  have hMfst : ∀ M b, (hM M b).fst = algebraMap B K b := fun M b => by
    simp [hM, ρ, RingHom.algebraMap_toAlgebra]
  have hR0 : ∀ a : R₀, (R (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hR a)
    simpa using this
  have hMc : ∀ M (a : R₀), (hM M (algebraMap R₀ B a)).snd = 0 := fun M a => by
    simp [hM, hR0 a]
  let D : (ι → K) → Derivation R₀ B K := fun M => derOf (hM M) (hMfst M) (hMc M)
  have hD : ∀ M x, D M x = ∑ i, M i * D (Pi.single i 1) x := by
    intro M x
    simp [D, derOf, hM, Fintype.linearCombination_apply, Pi.single_apply, mul_comm]
  let w : ι → (Fin n → K) := fun i j => (D (Pi.single i 1)).liftKaehlerDifferential (e j)
  let L := Fintype.linearCombination K w
  have hL : ∀ M, L M = fun j => (D M).liftKaehlerDifferential (e j) := by
    intro M
    funext j
    rw [liftKaehler_eq_sum (D M) (fun i => D (Pi.single i 1)) M (hD M)]
    simp [L, w, Fintype.linearCombination_apply, Finset.sum_apply]
  have Linj : Function.Injective L := by
    intro M M' hMM
    apply hinj
    apply derOf_injective (hM M) (hM M') (hMfst M) (hMc M) (hMfst M') (hMc M')
    apply derivation_eq_of_basis e
    intro j
    rw [hL, hL] at hMM
    exact congrFun hMM j
  have Lsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hcard])).mp Linj
  have hgfst' : ∀ b, (g b).fst = algebraMap B K b := fun b => hgfst b
  have hgc : ∀ a : R₀, (g (algebraMap R₀ B a)).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (hg a)
    simpa using this
  obtain ⟨M, hMeq⟩ := Lsurj (fun j => (derOf g hgfst' hgc).liftKaehlerDifferential (e j))
  refine ⟨M, ?_⟩
  refine derOf_injective g (hM M) hgfst' hgc (hMfst M) (hMc M) ?_
  apply derivation_eq_of_basis e
  intro j
  rw [hL] at hMeq
  exact (congrFun hMeq j).symm

end FirstOrderPoints

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolic
section
namespace GlobalTheory

theorem stab_relIndex_ne_zero : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  intro P M N _ _ _ s π u _ _ _ KP KM L _ _ _ TM hU q X
  obtain ⟨U, hUK, hUi, hUk⟩ := hU X
  set S := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM
  set C := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)
  have hUC : U ≤ C := by
    intro k hk
    simp only [C, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hUk k hk
  have hSK : S ≤ KM := inf_le_right
  have hUS : U.relIndex S ≠ 0 := fun h =>
    hUi (Subgroup.relIndex_eq_zero_of_le_right hSK h)
  have hCS : C.relIndex S ≠ 0 := fun h =>
    hUS (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_of_le_left S hUC))
  rw [Subgroup.inf_relIndex_left]
  exact hCS

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExists
section
namespace GlobalTheory

theorem stable_complement_of_kernel_exists
    (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
    (hι : Function.Injective ι) (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V)
    (hfin : FiniteDimensional ℂ H0) (A : Set (Module.End ℂ V))
    (h1 : ∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0)
    (h2 : ∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0)
    (h3 : ∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) :
    ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧
      ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  intro h hh
  set K : Submodule ℂ V := H0 ⊓ LinearMap.ker pr with hK
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  set K' : Submodule ℂ H := K.map ι with hK'
  haveI : FiniteDimensional ℂ K' := inferInstance
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, e, he, hsum⟩ := K'.exists_add_mem_mem_orthogonal (ι h)
  obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
  have hkH0 : k ∈ H0 := hk.1
  have hkker : pr k = 0 := hk.2
  refine ⟨h - k, H0.sub_mem hh hkH0, by simp [hkker], ?_⟩
  have horth : ∀ k' ∈ K, inner ℂ (ι k') (ι (h - k)) = 0 := by
    intro k' hk'
    have : ι (h - k) = e := by rw [map_sub, hsum]; abel
    rw [this]
    exact (Submodule.mem_orthogonal K' e).mp he _ (Submodule.mem_map_of_mem hk')
  intro a ha z hz
  set c := h - k with hc
  have hcH0 : c ∈ H0 := H0.sub_mem hh hkH0
  set d := a c - z • c with hd
  have hdK : d ∈ K := by
    refine ⟨H0.sub_mem (h1 a ha c hcH0) (H0.smul_mem z hcH0), ?_⟩
    show pr d = 0
    simp [hd, hz]
  obtain ⟨b, hb, hab⟩ := h3 a ha
  have hdorth : ∀ k' ∈ K, inner ℂ (ι k') (ι d) = 0 := by
    intro k' hk'
    have hbk : b k' ∈ K := ⟨h1 b hb k' hk'.1, h2 b hb k' hk'.1 hk'.2⟩
    have e1 : inner ℂ (ι k') (ι (a c)) = 0 := by
      rw [← inner_conj_symm, hab, inner_conj_symm]
      exact horth _ hbk
    rw [hd, map_sub, inner_sub_right, e1, map_smul, inner_smul_right, horth k' hk']
    simp
  have : ι d = 0 := inner_self_eq_zero.mp (hdorth d hdK)
  have hd0 : d = 0 := hι (by rw [this, map_zero])
  exact sub_eq_zero.mp hd0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

universe u

theorem ringHom_formallyEtale_of_ringEquiv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) : (e : S →+* T).FormallyEtale := by
  algebraize [(e : S →+* T)]
  exact Algebra.FormallyEtale.of_equiv (R := S) (A := S) (B := T)
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem ringHom_formallyEtale_respectsIso : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by
  have hiso := @ringHom_formallyEtale_of_ringEquiv.{u}
  constructor
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp hf (hiso e)
  · intro R S T _ _ _ f e hf
    exact RingHom.FormallyEtale.comp (hiso e) hf

theorem formallyEtale_localRingHom_of_etale {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale := by
  algebraize [f]
  let Rₓ := Localization.AtPrime (J.comap f)
  let Sₓ := Localization.AtPrime J
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyEtale R Sₓ := inferInstance
  have : Algebra.FormallyEtale Rₓ Sₓ :=
    Algebra.FormallyEtale.localization_base (J.comap f).primeCompl
  exact (RingHom.formallyEtale_algebraMap (R := Rₓ) (S := Sₓ)).2 this

theorem formallyEtale_stalkMap_of_etale {X Y : Scheme.{0}} (g : X ⟶ Y) [Etale g] (x : X) :
    (g.stalkMap x).hom.FormallyEtale :=
  HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale) (Q := RingHom.Etale)
    ringHom_formallyEtale_respectsIso
    (fun f hf J _ => formallyEtale_localRingHom_of_etale f hf J) ‹_› x

theorem stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U,
      (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧
        (f.stalkMap y).hom.EssFiniteType := by
  intro M W f U hg y hy
  have key : ∀ (x : M) (z : U), U.ι z = x →
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyEtale ∧
        (f.stalkMap x).hom.EssFiniteType := by
    intro x z hz
    subst hz
    have h1 := Flat.stalkMap (U.ι ≫ f) z
    have h2 := formallyEtale_stalkMap_of_etale (U.ι ≫ f) z
    have h3 := LocallyOfFiniteType.stalkMap (U.ι ≫ f) z
    have e := Scheme.Hom.stalkMap_comp U.ι f z
    rw [e] at h1 h2 h3
    have : IsIso (U.ι.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    refine ⟨?_, ?_, ?_⟩
    · exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).1 h1
    · exact (ringHom_formallyEtale_respectsIso.cancel_right_isIso _ _).1 h2
    · exact (RingHom.EssFiniteType.respectsIso.cancel_right_isIso _ _).1 h3
  exact key y ⟨y, hy⟩ (by simp)

end GlobalTheory
end

