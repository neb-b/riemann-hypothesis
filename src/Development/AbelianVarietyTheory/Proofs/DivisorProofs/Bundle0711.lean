module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Formalism.HermitianLattices.FinalMass
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNormLtOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes

namespace GlobalTheory.StdMassLower

section
variable {E : Type} [Field E] [NumberField E]

theorem eq_zero_of_norm_lt_one (z : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (z : E)‖ < 1) : z = 0 := by
  classical
  by_contra hz
  have h0 : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.2 hz
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ z : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (z : E))
  rw [← Algebra.coe_norm_int, norm_prod] at h2
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ < 1 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ ≤ ‖τ.toRatAlgHom (z : E)‖ := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ.toRatAlgHom)]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun σ _ => (h σ.toRingHom).le)
      _ < 1 := h τ
  rw [← h2] at h3
  simp only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast] at h3
  linarith

theorem eq_of_mk_eq (x y : 𝓞 E) (hx : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ ≤ 1) (hy : ∀ φ : E →+* ℂ, ‖φ (y : E)‖ ≤ 1)
    (h : Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) x = Ideal.Quotient.mk _ y) : x = y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  have : z = 0 := eq_zero_of_norm_lt_one z fun φ => by
    have e : φ (x : E) - φ (y : E) = 3 * φ (z : E) := by
      have := congrArg (fun t : 𝓞 E => φ (algebraMap (𝓞 E) E t)) hz
      simpa only [map_sub, map_mul, map_ofNat] using this
    have e2 := norm_sub_le (φ (x : E)) (φ (y : E))
    rw [e, norm_mul] at e2
    have := hx φ
    have := hy φ
    simp only [Complex.norm_ofNat] at e2
    linarith
  rw [this, mul_zero] at hz
  exact sub_eq_zero.1 hz

theorem card_quot_three :
    Nat.card (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) = 3 ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : (3 : 𝓞 E) = algebraMap ℤ (𝓞 E) 3 := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

theorem coord_of_mem {n : ℕ} {x : Fin n → E} (hx : x ∈ Formalism.MainNotions.StandardLattice.stdLat E n) (i : Fin n) :
    ∃ a : 𝓞 E, (a : E) = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [← ha, ← hb]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by simp [← ha, Algebra.smul_def]⟩

theorem isLattice_std (n : ℕ) : Submodule.IsFullLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  have : Submodule.IsLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) :=
    Submodule.IsLattice.of_fg E (Submodule.fg_span (Set.finite_range _))
  refine { span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  exact Submodule.subset_span ⟨j, rfl⟩

variable [StarRing E]

omit [NumberField E] in
theorem re_form (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (τ : E →+* ℂ) : (τ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re = ∑ i, Complex.normSq (τ (x i)) := by
  change (τ (∑ i, star (x i) * x i)).re = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem trace_pos (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (Formalism.MainNotions.StandardLattice.stdForm E n x x) := by
  have h1 := congrArg Complex.re
    (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := Formalism.MainNotions.StandardLattice.stdForm E n x x))
  rw [Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine Finset.sum_pos (fun σ _ => ?_) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
    refine lt_of_lt_of_eq ?_ (re_form hφ x σ.toRingHom).symm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero σ.toRingHom).2 hi)
  rw [← h1] at h2
  simpa using h2

omit [NumberField E] in
theorem isSymm_std (n : ℕ) : (Formalism.MainNotions.StandardLattice.stdForm E n).IsSymm := by
  constructor
  intro x y
  change starRingEnd _ (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star]


omit [NumberField E] in
theorem norm_entry_le (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (Formalism.MainNotions.StandardLattice.stdForm E n)) (j i : Fin n)
    (τ : E →+* ℂ) : ‖τ (g (Pi.single j 1) i)‖ ≤ 1 := by
  have e : Formalism.MainNotions.StandardLattice.stdForm E n (g (Pi.single j 1)) (g (Pi.single j 1)) = 1 := by
    rw [hg]
    change ∑ i, star ((Pi.single j (1 : E) : Fin n → E) i) * (Pi.single j (1 : E) : Fin n → E) i = 1
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h1 := re_form hφ (g (Pi.single j 1)) τ
  rw [e, map_one, Complex.one_re] at h1
  have h2 := Finset.single_le_sum (f := fun i => Complex.normSq (τ (g (Pi.single j 1) i)))
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 h2

theorem card_aut_std (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) (n : ℕ) :
    Finite (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ∧
    Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ≤
      3 ^ (Module.finrank ℚ E * n ^ 2) := by
  have hm : ∀ (g : Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) (j i : Fin n),
      ∃ a : 𝓞 E, (a : E) = g.1 (Pi.single j 1) i := fun g j i => by
    refine coord_of_mem ?_ i
    exact g.2.2.le ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  choose a ha using hm
  have hq := card_quot_three (E := E)
  haveI : Finite (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hq]; positivity)
  have hinj : Function.Injective fun g j i => Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) (a g j i) := by
    intro g g' h
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    funext i
    rw [Pi.basisFun_apply]
    change g.1 _ i = g'.1 _ i
    rw [← ha, ← ha, eq_of_mk_eq (a g j i) (a g' j i) (fun φ => ?_) (fun φ => ?_) (congrFun (congrFun h j) i)]
    · rw [ha]; exact norm_entry_le hφ g.2.1 j i φ
    · rw [ha]; exact norm_entry_le hφ g'.2.1 j i φ
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans_eq ?_⟩
  rw [Nat.card_fun, Nat.card_fun, hq, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← pow_mul, sq]

end

theorem card_aut_gmap {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (N : Submodule (𝓞 K) V) :
    Nat.card (Formalism.ThetaLiftIndependence.autL h N) = Nat.card (Formalism.ThetaLiftIndependence.autL h (Formalism.HermitianLatticesTheory.gmap g N)) := by
  have hmul : ∀ (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V),
      Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := fun a b M => by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ M : Submodule (𝓞 K) V, Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := fun M => Submodule.map_id M
  refine Nat.card_congr
    { toFun := fun u => ⟨g * u.1 * g⁻¹, mul_mem (mul_mem hg u.2.1) (inv_mem hg), ?_⟩
      invFun := fun u => ⟨g⁻¹ * u.1 * g, mul_mem (mul_mem (inv_mem hg) u.2.1) hg, ?_⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  · rw [← hmul, inv_mul_cancel_right, hmul, u.2.2]
  · rw [hmul, hmul, u.2.2, ← hmul, inv_mul_cancel, hone]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E], (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ, ((3 : ℝ) ^ (Module.finrank ℚ E * n ^ 2))⁻¹ ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  intro E _ _ _ _ hst n
  have hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := fun φ a => by
    rw [hst, IsCMField.complexEmbedding_complexConj]
  obtain ⟨⟨s, hs⟩, hm, -⟩ := Formalism.HermitianLatticesTheory.final_massBasic E (Fin n → E) _ (isSymm_std n) (trace_pos hφ) _
    (isLattice_std n)
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 (Formalism.MainNotions.StandardLattice.stdLat E n)
    ⟨isLattice_std n, fun p _ => ⟨1, one_mem _, Submodule.map_id _⟩⟩
  obtain ⟨hf, hc⟩ := card_aut_std hφ n
  haveI : Nonempty (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) :=
    ⟨⟨1, one_mem _, Submodule.map_id _⟩⟩
  have hp : 0 < Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) := Nat.card_pos
  rw [hm s hs]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun M => ((Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) M) : ℝ))⁻¹) (fun _ _ => by positivity) hN)
  beta_reduce
  rw [card_aut_gmap _ hg N, e]
  exact inv_anti₀ (by exact_mod_cast hp) (by exact_mod_cast hc)

end GlobalTheory.StdMassLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M hY q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨m, d, hd⟩ := exists_isCl_of_isProjOver hY
  obtain ⟨i, hi⟩ := hd.1 (genericPoint Y.Z)
  obtain ⟨U, hU, hD, hR⟩ := hd.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, M.isOpen_setOf_div d i⟩) (x := genericPoint M.Z)
      (div_genericPoint hi.1)
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hD ▸ hi⟩ (V := V) ⟨z, hz⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_mem_adjoin (M' := M) (φ := AlgHom.id o Ω) (t := d) (i := i) (z := w) (hle hw) (hR ▸ hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := _root_.GlobalTheory.PDA.exists_dividedPowers_aug B Q
  obtain ⟨ε, hε⟩ := (_root_.GlobalTheory.PDA.PDPoly.exists_lift_and_aug B Q).2
  obtain ⟨θ, hθ, hθη⟩ := _root_.GlobalTheory.SplitDP.exists_dp_ext B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLattice
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

namespace GlobalTheory.Dict.ThetaHalf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem EF_inv_smul (X : Data E r) (M : ℕ) (u v : Fin r → E) :
    EF X ((M : E)⁻¹ • u) v = (M : ℚ)⁻¹ * EF X u v := by
  have h : (M : E)⁻¹ • u = (M : ℚ)⁻¹ • u := by
    funext j
    simp [Rat.smul_def]
  rw [h, TensLat.EF_eq_bilin, TensLat.EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem mem_smul_iff (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) (x : Fin r → E) :
    x ∈ 𝔪 • L ↔ ∀ y ∈ 𝔪 • L, ∃ k : ℤ, (M : ℚ)⁻¹ * EF X x y = k := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on hx (fun a ha u hu => ?_) fun x₁ x₂ h₁ h₂ => ?_
    · refine Submodule.smul_induction_on hy (fun b hb v hv => ?_) fun y₁ y₂ h₁ h₂ => ?_
      · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
        have hb' : b' ∈ conjI 𝔪 := Ideal.subset_span ⟨b, hb, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (h𝔪 ▸ Ideal.mul_mem_mul ha hb')
        have ht' : (t : E) * M = a * cc (b : E) := by
          have h5 := congrArg (algebraMap (𝓞 E) E) ht
          rw [map_mul, map_mul, map_natCast] at h5
          exact h5
        obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem t hu) v hv
        refine ⟨k, ?_⟩
        rw [← hk, ← EF_inv_smul]
        change EF X ((M : E)⁻¹ • (a : E) • u) ((b : E) • v) = EF X ((t : E) • u) v
        rw [← hcc (b : E), ← TensLat.EF_smul, smul_smul, smul_smul]
        congr 2
        field_simp
        linear_combination -ht'
      · obtain ⟨k₁, h₁⟩ := h₁
        obtain ⟨k₂, h₂⟩ := h₂
        refine ⟨k₁ + k₂, ?_⟩
        rw [Int.cast_add, ← h₁, ← h₂]
        simp only [TensLat.EF_eq_bilin, map_add (f := _), mul_add]
    · obtain ⟨k₁, h₁⟩ := h₁
      obtain ⟨k₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, ?_⟩
      rw [Int.cast_add, ← h₁, ← h₂]
      simp only [TensLat.EF_eq_bilin, map_add (f := _), mul_add, LinearMap.add_apply]
  · intro h
    have h1 : ∀ b ∈ conjI 𝔪, b • (M : E)⁻¹ • x ∈ L := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨a, ha, hb⟩ := hb
        refine (hL.2 _).2 fun u hu => ?_
        obtain ⟨k, hk⟩ := h _ (Submodule.smul_mem_smul ha hu)
        refine ⟨k, ?_⟩
        change EF X ((b : E) • (M : E)⁻¹ • x) u = k
        rw [hb, TensLat.EF_smul, hcc, EF_inv_smul]
        exact hk
      | zero => simp
      | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
      | smul t a _ ha => rw [smul_eq_mul, mul_smul]; exact L.smul_mem t ha
    have h2 : ∀ c ∈ 𝔪 * conjI 𝔪, c • (M : E)⁻¹ • x ∈ 𝔪 • L := by
      intro c hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c₁ c₂ h₁ h₂ => ?_
      · rw [mul_smul]; exact Submodule.smul_mem_smul ha (h1 b hb)
      · rw [add_smul]; exact add_mem h₁ h₂
    have h3 := h2 M (h𝔪 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (M : 𝓞 E) • (M : E)⁻¹ • x = x := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME,
        one_smul]
    rwa [h4] at h3

theorem span_smul (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) :
    Submodule.span E ((𝔪 • L : Lt E r) : Set (Fin r → E)) = ⊤ := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMm : (M : 𝓞 E) ∈ 𝔪 := by
    refine Ideal.mul_le_left (J := conjI 𝔪) ?_
    rw [h𝔪]
    exact Ideal.mem_span_singleton_self _
  rw [eq_top_iff, ← TensLat.span_of_selfD X hL, Submodule.span_le]
  intro u hu
  have h1 : (M : E)⁻¹ • (M : 𝓞 E) • u = u := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME,
      one_smul]
  have h2 : (M : 𝓞 E) • u ∈ 𝔪 • L := Submodule.smul_mem_smul hMm hu
  have h3 := Submodule.smul_mem _ (M : E)⁻¹ (Submodule.subset_span (R := E) h2)
  rw [h1] at h3
  exact h3

theorem exists_ne_zero_of_scaled {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : ℕ} (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (hp : Function.Injective p)
    (L : Submodule ℤ V) (hfg : L.FG) {M : ℕ} (hM : 2 ≤ M)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, (M : ℚ)⁻¹ * B x y = k)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ = 1) {f : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ v ∈ L, ∀ z, f (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) :
    ∃ v ∈ L, f ((M : ℂ)⁻¹ • p v) ≠ 0 := by
  have hM0 : M ≠ 0 := by omega
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hMR : (0 : ℝ) < (M : ℝ)⁻¹ := by positivity
  have hsc : ∀ z u : Fin g → ℂ, z ⬝ᵥ ((M : ℝ)⁻¹ • Hm).mulVec u = (M : ℝ)⁻¹ • (z ⬝ᵥ Hm.mulVec u) :=
    fun z u => by rw [smul_mulVec, dotProduct_smul]
  refine _root_.GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual V g ((M : ℚ)⁻¹ • B) p hp L hfg hL hsp ((M : ℝ)⁻¹ • Hm) ?_ (fun z hz => ?_)
    (fun u v => ?_) c hc M hM f hd h0 fun v hv z => ?_
  · ext i j
    rw [conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_smul, hH.apply, star_trivial]
  · rw [hsc, smul_re, smul_eq_mul]
    exact mul_pos hMR (hpos z hz)
  · rw [hsc, smul_im, LinearMap.smul_apply, LinearMap.smul_apply, hB]
    simp
  · rw [hf v hv z, hsc, hsc]
    congr 3
    simp only [real_smul]
    push_cast
    field_simp

theorem exists_ne_zero_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs w L hL x hx' 𝔪 M hM h𝔪 θ hθ h0
  have hM0 : M ≠ 0 := by omega
  obtain ⟨hconj, hpos, him, -, hsm, hinj, hspan, -⟩ :=
    GlobalTheory.Dict.hx_laws E r X g bas idx 0 hs Even.zero x hx'
  set Hm := (hMat X bas idx x)ᵀ * imInv X bas idx x * (hMat X bas idx x).map star with hHm
  have hform : ∀ z u, hx X bas idx x z u = z ⬝ᵥ Hm.mulVec (star u) := fun z u =>
    SiegelNormalForm.form_pull _ _ z u
  have hH : Hm.IsHermitian := by
    ext i j
    have := hconj (Pi.single j 1) (Pi.single i 1)
    rw [hform, hform, SiegelNormalForm.form_single, SiegelNormalForm.form_single] at this
    exact this.symm
  clear_value Hm
  let p : (Fin r → E) →ₗ[ℤ] (Fin g → ℂ) := (AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl).toIntLinearMap
  have hp : ∀ v, p v = pv X idx x v := fun _ => rfl
  have hne : ∀ v, eps1 X w v ≠ 0 := fun v => Complex.exp_ne_zero _
  have key : ∀ v ∈ L, ∀ z, θ (z + p v) =
      ((eps1 X w v)⁻¹ * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * θ z := by
    intro v hv z
    have h1 := congrFun (hθ.2 v hv) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hform, add_dotProduct, smul_dotProduct] at h1
    rw [← h1, ← hp, _root_.mul_mul_mul_comm, inv_mul_cancel₀ (hne v), _root_.one_mul,
      ← _root_.mul_assoc, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans ?_
    congr 1
    refine Complex.exp_zero.symm.trans (congrArg _ ?_)
    push_cast
    ring
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_scaled (traceFormBilin (X.κ0 / 2) X.Gm) p hinj
    ((𝔪 • L).restrictScalars ℤ)
    (Submodule.FG.of_le hL.1 (Submodule.smul_le_right (I := 𝔪))).restrictScalars hM
    (fun u => by simp only [← TensLat.EF_eq_bilin]; exact mem_smul_iff X hL hM0 h𝔪 u)
    (hspan _ (span_smul X hL hM0 h𝔪)).1 hH (fun z hz => hform z z ▸ hpos z hz)
    (fun u v => by rw [← TensLat.EF_eq_bilin, ← him, hform, hp, hp])
    (fun v => (eps1 X w v)⁻¹)
    (fun v => by
      have : eps1 X w v = cexp ((Real.pi * (EF X v (w • v) : ℚ) : ℝ) * I) := by
        unfold eps1; congr 1; push_cast; ring
      rw [norm_inv, this, Complex.norm_exp_ofReal_mul_I, inv_one])
    hθ.1 h0 (fun v hv => key v (Submodule.smul_le_right (I := 𝔪) hv))
  refine ⟨u, hu, ?_⟩
  have e : pv X idx x ((M : E)⁻¹ • u) = (M : ℂ)⁻¹ • p u := by
    rw [hsm]
    funext j
    rw [map_inv₀, map_natCast, hp, Pi.smul_apply, smul_eq_mul]
  rwa [e]

end GlobalTheory.Dict.ThetaHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  first | (exact @GlobalTheory.EtC.kum_surjective) | (exact GlobalTheory.EtC.kum_surjective) | (intros; apply GlobalTheory.EtC.kum_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
section
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k (GlobalTheory.CuspRep.lie E a X φ))) := by
  first | exact @GlobalTheory.CuspRep.KFin.kfin_lie | exact GlobalTheory.CuspRep.KFin.kfin_lie | (intros; apply GlobalTheory.CuspRep.KFin.kfin_lie <;> assumption)
end

