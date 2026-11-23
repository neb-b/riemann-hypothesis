module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct Topology

namespace GlobalTheory.IntDense

theorem mem_of_isClosed (F : Type) [Field F] [NumberField F] {C : Set (FiniteAdeleRing (𝓞 F) F)}
    (hC : IsClosed C) (h : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ C)
    (α : FiniteAdeleRing (𝓞 F) F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) : α ∈ C := by
  by_contra hn
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F => α - y := continuous_const.sub continuous_id
  have hU : (fun y : FiniteAdeleRing (𝓞 F) F => α - y) ⁻¹' Cᶜ ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (hC.isOpen_compl.preimage hc).mem_nhds (by simpa using hn)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
  refine hNU β hβ ?_
  change α - N • β ∈ C
  rw [e, add_sub_cancel_right]
  exact h a

theorem addChar_eq_one_of_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  intro F _ _ ψ hψ x h α hα
  have hp : Continuous fun y : Af F => pairA F 0 (y * algebraMap F (Af F) x) :=
    Continuous.prodMk continuous_const (continuous_id.mul continuous_const)
  refine mem_of_isClosed F (C := {y | ψ (pairA F 0 (y * algebraMap F (Af F) x)) = 1})
    (isClosed_eq (hψ.comp hp) continuous_const) (fun a => ?_) α hα
  have := h a
  rwa [map_mul] at this

end GlobalTheory.IntDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinMod

open GlobalTheory.LatVac

theorem exists_finite_mod {W : Type} [AddCommGroup W] {G : Set W} (hG : G.Finite) {k : ℕ} (hk : 0 < k) :
    ∃ R : Set W, R.Finite ∧ ∀ x ∈ Submodule.span ℤ G, ∃ r ∈ R, ∃ u ∈ Submodule.span ℤ G, x = r + k • u := by
  induction G, hG using Set.Finite.induction_on with
  | empty => exact ⟨{0}, Set.finite_singleton _, fun x hx => ⟨0, rfl, 0, zero_mem _, by simpa using hx⟩⟩
  | @insert g G _ _ ih =>
    obtain ⟨R, hR, h⟩ := ih
    refine ⟨Set.image2 (fun (j : ℤ) r => j • g + r) (Set.Ico 0 k) R, (Set.finite_Ico _ _).image2 _ hR,
      fun x hx => ?_⟩
    obtain ⟨c, y, hy, rfl⟩ := Submodule.mem_span_insert.1 hx
    obtain ⟨r, hr, u, hu, rfl⟩ := h y hy
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    refine ⟨_, ⟨c % k, ⟨Int.emod_nonneg _ hk'.ne', Int.emod_lt_of_pos _ hk'⟩, r, hr, rfl⟩,
      (c / k) • g + u, Submodule.mem_span_insert.2 ⟨_, u, hu, rfl⟩, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv c k]
    simp only [add_smul, mul_smul, smul_add, natCast_zsmul]
    abel

theorem exists_int_gen {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module (𝓞 E) M]
    (N : Submodule (𝓞 E) M) (hN : N.FG) :
    ∃ A : Set M, A.Finite ∧ A ⊆ N ∧ ∀ x ∈ N, x ∈ Submodule.span ℤ A := by
  have h1 : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have h2 : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨s, hs⟩ := h2.fg_top
  refine ⟨Subtype.val '' (s : Set N), s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · have : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (s : Set N) := by rw [hs]; trivial
    exact Submodule.apply_mem_span_image_of_mem_span (N.subtype.toAddMonoidHom.toIntLinearMap) this

theorem triadd_mem_span {X Y Z W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    (f : X → Y → Z → W) (h1 : ∀ a a' s t, f (a + a') s t = f a s t + f a' s t)
    (h2 : ∀ a s s' t, f a (s + s') t = f a s t + f a s' t) (h3 : ∀ a s t t', f a s (t + t') = f a s t + f a s t')
    {A : Set X} {B : Set Y} {C : Set Z} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    f a s t ∈ Submodule.span ℤ ((fun p : X × Y × Z => f p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  have gen : ∀ {U : Type} [AddCommGroup U] (g : U → W), (∀ u u', g (u + u') = g u + g u') →
      ∀ (N : Submodule ℤ W) (V : Set U), (∀ u ∈ V, g u ∈ N) → ∀ u ∈ Submodule.span ℤ V, g u ∈ N := by
    intro U _ g hg N V hV u hu
    have : Submodule.span ℤ V ≤ N.comap (AddMonoidHom.mk' g hg).toIntLinearMap := Submodule.span_le.2 hV
    exact this hu
  refine gen (fun a => f a s t) (fun a a' => h1 a a' s t) _ A (fun a ha => ?_) a ha
  refine gen (fun s => f a s t) (fun s s' => h2 a s s' t) _ B (fun s hs => ?_) s hs
  refine gen (fun t => f a s t) (h3 a s) _ C (fun t ht => ?_) t ht
  exact Submodule.subset_span ⟨(a, s, t), ⟨ha, hs, ht⟩, rfl⟩

theorem star_sum_add {E : Type} [CommRing E] [StarRing E] {n : ℕ} (c : E) (s s' g : Fin n → E) :
    c * ∑ k, star ((s + s') k) * g k = c * ∑ k, star (s k) * g k + c * ∑ k, star (s' k) * g k := by
  simp [mul_add, add_mul, Finset.sum_add_distrib]

theorem pair_tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (ε β : Af F) (x : F) (k : ℕ) (a t g : E) :
    pairA F 0 (ε * (algebraMap F _ x + k • β)) ⊗ₜ[F] (a * t * g) =
      pairA F 0 ε ⊗ₜ[F] (algebraMap F E x * a * t * g) + k • (pairA F 0 (ε * β) ⊗ₜ[F] (a * t * g)) := by
  have hp : pairA F 0 (ε * (algebraMap F _ x + k • β)) = x • pairA F 0 ε + k • pairA F 0 (ε * β) := by
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = x • 0 + k • 0
      simp
    · change ε * (algebraMap F _ x + k • β) = x • ε + k • (ε * β)
      rw [mul_add, mul_smul_comm, Algebra.smul_def x, mul_comm ε]
  rw [hp, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def x,
    ← mul_assoc, ← mul_assoc]

theorem add_nsmul_residue_add {W : Type} [AddCommGroup W] (k : ℕ) (y u y' u' : W) :
    y + k • u + (y' + k • u') = y + y' + k • (u + u') := by rw [smul_add]; abel

theorem neg_nsmul_residue {W : Type} [AddCommGroup W] (k : ℕ) (y u : W) : -(y + k • u) = -y + k • -u := by
  rw [smul_neg]; abel

theorem add_nsmul_residue_assoc {W : Type} [AddCommGroup W] (k : ℕ) (r u' u : W) :
    r + k • u' + k • u = r + k • (u' + u) := by rw [smul_add, add_assoc]

variable {D : D7}

theorem genMap_mem_span (S T : HSp D) {A : Set D.host.E} {B : Set (Fin S.rank → D.host.E)}
    {C : Set (Fin T.rank → D.host.E)} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    genMap S T a s t ∈ Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  refine triadd_mem_span (genMap S T) (fun a a' s t => ?_) (fun a s s' t => ?_) (fun a s t t' => ?_) ha hs ht
  · exact Matrix.ext fun i j => (congrArg (· * _) (add_mul a a' (t i))).trans (add_mul _ _ _)
  · exact Matrix.ext fun i j => star_sum_add (a * t i) s s' fun k => S.gram k j
  · exact Matrix.ext fun i j => (congrArg (· * _) (mul_add a (t i) (t' i))).trans (add_mul _ _ _)


open Classical in
def idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop)
    (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemAt F P) = if P v then 1 else 0 := rfl

theorem latO_finite_mod : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ΛS.FG → ΛT.FG → ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (k : ℕ), 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, ∃ r ∈ R, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, t = r + k • u := by
  intro D S T ΛS ΛT hS hT P k hk
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ Submodule.span ℤ G, x ∈ Λ := by
    have : Submodule.span ℤ G ≤ Λ.toIntSubmodule := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
      exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    exact fun x hx => this hx
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨R, hR, h⟩ := exists_finite_mod hG hk
  refine ⟨R, hR, fun w hw => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  obtain ⟨r, hr, u', hu', rfl⟩ := h y hy
  exact ⟨r, hr, u' + u, add_mem (hGΛ _ hu') hu, add_nsmul_residue_assoc k r u' u⟩

end GlobalTheory.LatFinMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacDual

theorem exists_extension {O E V : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (Λ : Submodule O V) (hspan : Submodule.span E (Λ : Set V) = ⊤) (φ : Λ →ₗ[O] O) :
    ∃ ψ : V →ₗ[E] E, ∀ x : Λ, ψ x = algebraMap O E (φ x) := by
  haveI : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun x => by
        rw [Module.End.isUnit_iff]
        have hx : algebraMap O E x ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
        refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap O E x)⁻¹ • b, ?_⟩⟩
        · have h' : algebraMap O E x • a = algebraMap O E x • b := by
            simpa [Module.algebraMap_end_apply] using h
          exact smul_right_injective V hx h'
        · rw [Module.algebraMap_end_apply, ← algebraMap_smul E, smul_smul, mul_inv_cancel₀ hx, one_smul]
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set V) := hspan ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun {a b} h => ⟨1, by rw [Λ.injective_subtype h]⟩ }
  let g : V →ₗ[O] E := IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
    ((Algebra.linearMap O E).comp φ) (IsLocalizedModule.map_units (Algebra.linearMap O E))
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype ((Algebra.linearMap O E).comp φ)
    (IsLocalizedModule.map_units (Algebra.linearMap O E)) x

theorem exists_dual_family {E : Type} [Field E] [NumberField E] [StarRing E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (hG : ∀ i j, star (G i j) = G j i) (hdet : IsUnit G.det)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hsd : ∀ y : Fin r → E, (∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) → y ∈ Λ) :
    ∃ (n : ℕ) (s s' : Fin n → Fin r → E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧
      ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * G k j = if a = j then 1 else 0 := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose ψ hψ using fun i : Fin n => exists_extension Λ hspan ((LinearMap.proj i).comp σ)
  let c : Fin n → Fin r → E := fun i j => ψ i (Pi.single j 1)
  have hc : ∀ i x, ψ i x = ∑ j, x j * c i j := by
    intro i x
    conv_lhs => rw [pi_eq_sum_univ' x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [c, map_sum]
  let s' : Fin n → Fin r → E := fun i => star (c i ᵥ* G⁻¹)
  have hs' : ∀ i j, ∑ k, star (s' i k) * G k j = c i j := by
    intro i j
    have : (c i ᵥ* G⁻¹) ᵥ* G = c i := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    rw [← congrFun this j]
    simp [s', Matrix.vecMul, dotProduct]
  let s : Fin n → Fin r → E := fun i => f (Pi.single i 1)
  refine ⟨n, s, s', fun i => ⟨(f (Pi.single i 1)).2, hsd _ fun x hx => ?_⟩, fun a j => ?_⟩
  · have h1 : ∑ a, ∑ b, star (x a) * G a b * s' i b = star (ψ i x) := by
      rw [hc, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hs', star_mul', star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', star_star, hG]; ring
    have h2 := hψ i ⟨x, hx⟩
    rw [h1]
    refine ⟨⟨star (ψ i x), ?_⟩, rfl⟩
    have h3 : IsIntegral ℤ (ψ i x) := by
      rw [show ψ i x = _ from h2]
      exact RingOfIntegers.isIntegral_coe _
    exact h3.map (starRingEnd E).toIntAlgHom
  · have key : (∑ i, (ψ i).smulRight (s i) : (Fin r → E) →ₗ[E] (Fin r → E)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun x hx => ?_
      have h1 : f (σ ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hσ ⟨x, hx⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pi_eq_sum_univ' (σ ⟨x, hx⟩), map_sum] at h1
      have h2 := congrArg Λ.subtype h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      rw [LinearMap.sum_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [LinearMap.smulRight_apply, show ψ i x = _ from hψ i ⟨x, hx⟩, algebraMap_smul, map_smul, map_smul]
      rfl
    have h := congrFun (LinearMap.congr_fun key (Pi.single j 1)) a
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.id_apply, Pi.single_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs', mul_comm]

theorem dualFamily : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S Λ → ∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0 := by
  intro D S Λ h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤ := by
    obtain ⟨t, ht⟩ := h.1.fg
    apply eq_top_iff.mpr
    intro y _
    let p : (Fin S.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * S.gram i j * y j
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) t p
    have hp : ∀ x ∈ Λ, IsIntegral ℤ ((b : 𝓞 D.host.E) • p x) := by
      intro x hx
      rw [← ht] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hb x hx
        rw [← ha]
        exact RingOfIntegers.isIntegral_coe a
      | zero => simpa [p] using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
      | add x z hx hz ihx ihz =>
        have heq : p (x + z) = p x + p z := by
          simp [p, star_add, add_mul, Finset.sum_add_distrib]
        rw [heq, smul_add]
        exact ihx.add ihz
      | smul c x hx ih =>
        have heq : p (c • x) = star (c : D.host.E) * p x := by
          simp only [p, Pi.smul_apply, algebraMap_smul, star_mul', Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          change star ((c : D.host.E) * x i) * S.gram i j * y j = _
          rw [star_mul']
          ring
        rw [heq, Algebra.smul_def]
        have hc := (RingOfIntegers.isIntegral_coe c).map (starRingEnd D.host.E).toIntAlgHom
        have hc' : IsIntegral ℤ (star (c : D.host.E)) := hc
        convert hc'.mul ih using 1 <;> simp only [Algebra.smul_def] <;> ring
    have hy : (b : 𝓞 D.host.E) • y ∈ Λ := (h.2 _).2 (by
      intro x hx
      have hi := hp x hx
      refine ⟨⟨_, ?_⟩, rfl⟩
      have heq : (∑ i, ∑ j, star (x i) * S.gram i j * ((b : 𝓞 D.host.E) • y) j) =
          (b : 𝓞 D.host.E) • p x := by
        simp only [p, Pi.smul_apply, algebraMap_smul, Algebra.smul_def, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
      change IsIntegral ℤ (∑ i, ∑ j, star (x i) * S.gram i j * ((b : 𝓞 D.host.E) • y) j)
      rw [heq]
      exact hi)
    have hb0 : (algebraMap (𝓞 D.host.E) D.host.E b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hy' : (b : 𝓞 D.host.E) • y ∈ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) :=
      Submodule.subset_span hy
    have hy'' : (algebraMap (𝓞 D.host.E) D.host.E b) • y ∈
        Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) := by
      simpa only [algebraMap_smul] using hy'
    have := (Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E b)⁻¹ hy''
    rw [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this
    exact this
  exact exists_dual_family S.gram (gram_star S) (gram_det_isUnit S) Λ h.1.fg hspan
    fun y hy => (h.2 y).2 hy

end GlobalTheory.LatVacDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSumIntegralBasis
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem isClosed_int_add_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (M : ℕ) (hM : 0 < M) (hcl : IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c}) :
    IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} := by
  have key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} =
      ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨z, c, hc, rfl⟩
      have hMz : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg z hMz.ne'
      have h1 : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMz
      have hdiv := congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv
      refine ⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩
      have hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      simp only [hr]
      linear_combination -hdiv
    · rintro ⟨r, c, hc, hx⟩
      refine ⟨((r : ℕ) : ℤ), c, hc, ?_⟩
      rw [Int.cast_natCast]
      linear_combination hx
  rw [key]
  exact isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)

theorem exists_sum_of_approx {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (hO : IsCompact (O : Set A))
    (hcl : ∀ M : ℕ, 0 < M → IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c})
    (hz : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c ∈ O, a = (M : A) * c) → a = 0)
    {β : Type} [Fintype β] (w : β → A) (a : A)
    (ha : ∀ M : ℕ, 0 < M → ∃ (z : β → ℤ) (c : A), c ∈ O ∧ a = ∑ i, (z i : A) * w i + (M : A) * c) :
    ∃ r : β → A, (∀ i, ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r i = (z : A) + (M : A) * c) ∧
      a = ∑ i, r i * w i := by
  classical
  have hSc : ∀ M : ℕ, 0 < M →
      IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} :=
    fun M hM => isClosed_int_add_mul O M hM (hcl M hM)
  have hL : Continuous fun r : β → A => a - ∑ i, r i * w i :=
    continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  let t : ℕ → Set (β → A) := fun m =>
    (⋂ i, (fun r : β → A => r i) ⁻¹'
      {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩
    (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter
      ((hcl (m + 1) m.succ_pos).preimage hL)
  have hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A)) := isCompact_univ_pi fun _ => hO
  have hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty := by
    intro u
    have hNpos : 0 < ∏ m ∈ u, (m + 1) := Finset.prod_pos fun m _ => m.succ_pos
    obtain ⟨z, c, hc, hac⟩ := ha _ hNpos
    refine ⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩
    simp only [Set.mem_iInter]
    intro m hm
    obtain ⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1) := Finset.dvd_prod_of_mem _ hm
    rw [hk] at hac
    simp only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩
    push_cast at hac ⊢
    linear_combination hac
  obtain ⟨r, -, hr⟩ := hs.inter_iInter_nonempty t htc hne
  simp only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr
  have hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1 := fun M hM => ⟨M - 1, by omega⟩
  refine ⟨r, fun i M hM => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hpred M hM
    exact (hr m).1 i
  · have h0 : a - ∑ i, r i * w i = 0 := hz _ fun M hM => by
      obtain ⟨m, rfl⟩ := hpred M hM
      exact (hr m).2
    exact sub_eq_zero.mp h0

private def intAdeles (F : Type) [Field F] [NumberField F] :
    Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' ha v := neg_mem (ha v)

theorem exists_sum_integralBasis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ r : β → FiniteAdeleRing (𝓞 F) F, (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) ∧ a = ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) := by
  intro F _ _ β _ ω a ha
  obtain ⟨hcomp, hclM, hzero, -, -, -⟩ := _root_.GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  have hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) =
      ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F) := by
    intro x
    conv_lhs => rw [← ω.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_
  intro M hM
  obtain ⟨x, c, hc, hac⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha
  refine ⟨fun i => ω.repr x i, c, hc, ?_⟩
  rw [hac, hexp, nsmul_eq_mul]

end GlobalTheory.ClassFin
end

