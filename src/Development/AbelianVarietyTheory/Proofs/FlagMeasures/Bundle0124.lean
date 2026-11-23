module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGenerators
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem basis_of_span_mod_uniformiser {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (L₁ : Submodule O (Fin n → K)) (hfg : L₁.FG)
    (hspan : Submodule.span K (L₁ : Set (Fin n → K)) = ⊤)
    (C : Fin n → Fin n → K) (hC : ∀ j, C j ∈ L₁) (g : O)
    (hg : IsLocalRing.maximalIdeal O = Ideal.span {g})
    (hmod : ∀ x ∈ L₁, ∃ s ∈ Submodule.span O (Set.range C), ∃ z ∈ L₁, x = s + (g : K) • z) :
    ∃ fr : GL (Fin n) K, (fr : Matrix (Fin n) (Fin n) K) = Matrix.of (fun a j => C j a) ∧
      ∀ x : Fin n → K, x ∈ L₁ ↔ ∀ a, ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x a ∈ O := by
  classical
  set M : Matrix (Fin n) (Fin n) K := Matrix.of (fun a j => C j a) with hM
  set N : Submodule O (Fin n → K) := Submodule.span O (Set.range C) with hN
  have hsm : ∀ (c : O) (y : Fin n → K), c • y = (c : K) • y := fun c y => rfl
  have hNL : N ≤ L₁ := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hC j)
  have hLN : L₁ ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      obtain ⟨s, hs, z, hz, rfl⟩ := hmod x hx
      refine Submodule.add_mem_sup hs ?_
      rw [← hsm]
      exact Submodule.smul_mem_smul (by rw [hg]; exact Ideal.mem_span_singleton_self g) hz
  have hCspan : Submodule.span K (Set.range C) = ⊤ := by
    rw [eq_top_iff, ← hspan, ← Submodule.span_span_of_tower O K (Set.range C)]
    exact Submodule.span_mono (fun x hx => hLN hx)
  have hMT : M.col = C := by ext j a; rfl
  have hsurj : Function.Surjective M.mulVec := by
    have h := Matrix.range_mulVecLin M
    rw [hMT, hCspan, LinearMap.range_eq_top] at h
    exact h
  have hunit : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  have hMv : ∀ w : Fin n → K, M *ᵥ w = ∑ j, w j • C j := by
    intro w; ext a
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinvM : ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M = 1 := hunit.unit.inv_mul
  have hMinv : M * ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := hunit.unit.mul_inv
  refine ⟨hunit.unit, rfl, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hLN hx)
    have hx' : x = M *ᵥ (fun j => (c j : K)) := by
      rw [hMv, ← hc]; simp only [hsm]
    intro a
    rw [hx', Matrix.mulVec_mulVec, hinvM, Matrix.one_mulVec]
    exact (c a).2
  · apply hNL
    set w := ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hw
    have hx' : x = M *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
    rw [hx', hMv]
    refine (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨fun j => ⟨w j, hx j⟩, ?_⟩
    simp only [hsm]

theorem first_components_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm n J _ _ v sp _ hsp1 hint g hg L hL c S hc hS hmod
  classical
  let πv : (Fin n → E ⊗[F] v.adicCompletion F) → (Fin n → v.adicCompletion F) := fun y a => (sp (y a)).1
  let ι : (Fin n → E) → (Fin n → E ⊗[F] v.adicCompletion F) := fun l i => l i ⊗ₜ[F] (1 : v.adicCompletion F)
  have hfstO : ∀ r : intV E v, (sp (r : E ⊗[F] v.adicCompletion F)).1 ∈ v.adicCompletionIntegers F :=
    fun r => ((hint r).mp r.2).1
  have hπsmul : ∀ (r : intV E v) (y : Fin n → E ⊗[F] v.adicCompletion F),
      πv (r • y) = (⟨_, hfstO r⟩ : v.adicCompletionIntegers F) • πv y := by
    intro r y; funext a
    change (sp ((r : E ⊗[F] v.adicCompletion F) * y a)).1 = (sp (r : E ⊗[F] v.adicCompletion F)).1 * (sp (y a)).1
    rw [map_mul, Prod.fst_mul]
  have hproj : ∀ (T : Set (Fin n → E ⊗[F] v.adicCompletion F)) (y), y ∈ Submodule.span (intV E v) T →
      πv y ∈ Submodule.span (v.adicCompletionIntegers F) (πv '' T) := by
    intro T y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : πv 0 = 0 := by funext a; simp [πv]
      rw [h0]; exact zero_mem _
    | add x y _ _ hx hy =>
      have h0 : πv (x + y) = πv x + πv y := by funext a; simp [πv]
      rw [h0]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [hπsmul]; exact Submodule.smul_mem _ _ hx
  have hιπ_add : ∀ x y : Fin n → E, πv (ι (x + y)) = πv (ι x) + πv (ι y) := by
    intro x y; funext a; simp [πv, ι, TensorProduct.add_tmul]
  have hιπ_zero : πv (ι 0) = 0 := by funext a; simp [πv, ι]
  have hιπ_smul : ∀ (e : E) (x : Fin n → E), πv (ι (e • x)) = (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 • πv (ι x) := by
    intro e x; funext a
    change (sp ((e * x a) ⊗ₜ[F] (1 : v.adicCompletion F))).1 =
      (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (sp (x a ⊗ₜ[F] (1 : v.adicCompletion F))).1
    rw [show (e * x a) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (e ⊗ₜ[F] (1 : v.adicCompletion F)) * (x a ⊗ₜ[F] (1 : v.adicCompletion F)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, Prod.fst_mul]
  have hφO : ∀ e : 𝓞 E, (sp ((e : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ∈ v.adicCompletionIntegers F := by
    intro e
    have hm : (e : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := by
      unfold intV tensInt
      exact Subring.subset_closure (Or.inl ⟨⟨(e : E), by unfold intOE; exact RingHom.mem_range.mpr ⟨e, rfl⟩⟩, rfl⟩)
    exact hfstO ⟨_, hm⟩
  have hι : ∀ l ∈ L, ι l ∈ loc v L := fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩
  let L₁ : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F) :=
    { carrier := {x | ∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a}
      add_mem' := by
        rintro x x' ⟨y, hy, hyx⟩ ⟨y', hy', hyx'⟩
        exact ⟨y + y', add_mem hy hy', fun a => by simp [hyx, hyx']⟩
      zero_mem' := ⟨0, zero_mem _, fun a => by simp⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hyx⟩
        have h1r : ((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) ∈ intV E v :=
          (hint _).mpr ⟨by rw [hsp1]; exact r.2, by rw [hsp1]; exact r.2⟩
        refine ⟨(⟨_, h1r⟩ : intV E v) • y, Submodule.smul_mem _ _ hy, fun a => ?_⟩
        change (sp (((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) * y a)).1 = (r : v.adicCompletion F) * x a
        rw [map_mul, Prod.fst_mul, hsp1, hyx a] }
  let C : Fin n → Fin n → v.adicCompletion F := fun j => πv (c j)
  have hC : ∀ j, C j ∈ L₁ := fun j => ⟨c j, hc j, fun a => rfl⟩
  have hfg : L₁.FG := by
    obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := L)).mp hL.1
    refine ⟨s.image (fun l => πv (ι l)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨ι l, hι l (hs ▸ Submodule.subset_span hl), fun a => rfl⟩
    · rintro x ⟨y, hy, hyx⟩
      have hx : x = πv y := funext fun a => (hyx a).symm
      rw [hx]
      refine (Submodule.span_le.mpr ?_) (hproj (ι '' (L : Set (Fin n → E))) y hy)
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [← hs] at hl
      induction hl using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx =>
        have h0 : πv (ι (e • x)) = (⟨_, hφO e⟩ : v.adicCompletionIntegers F) • πv (ι x) :=
          hιπ_smul (e : E) x
        rw [h0]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) = ⊤ := by
    have key : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        πv (ι x) ∈ Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨ι x, hι x hx, fun a => rfl⟩
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx => rw [hιπ_smul]; exact Submodule.smul_mem _ _ hx
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := key (fun j => if a = j then (1 : E) else 0) (by rw [hL.2]; trivial)
    convert h using 1
    funext j
    by_cases h' : a = j <;> simp [πv, ι, hsp1, h']
  have hmod' : ∀ x ∈ L₁, ∃ s ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range C), ∃ z ∈ L₁,
      x = s + (((g : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) • z := by
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨s, hs, z, hz, hyz⟩ := hmod y hy
    refine ⟨πv s, ?_, πv z, ⟨z, hz, fun a => rfl⟩, ?_⟩
    · refine (Submodule.span_le.mpr ?_) (hproj _ s hs)
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩ | hw
      · exact Submodule.subset_span ⟨j, rfl⟩
      · have h0 : πv w = 0 := funext fun a => hS w hw a
        rw [h0]; exact zero_mem _
    · funext a
      rw [← hyx a, hyz]
      simp [πv]
  obtain ⟨fr, hfr, hmem⟩ :=
    basis_of_span_mod_uniformiser (v.adicCompletionIntegers F) L₁ hfg hspan C hC _ hg hmod'
  exact ⟨fr, hfr, hmem⟩

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIff
section
open NumberField

namespace GlobalTheory.RowLatXS

private theorem coefX_add_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) (hy : y ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  have hxy : x + y ∈ Submodule.span E (Set.range F.e) := Submodule.add_mem _ hx hy
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hxy]
  have hsum : (⟨x + y, hxy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [hsum, map_add (f := _), Finsupp.add_apply]

private theorem coefX_smul_flag_measures {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) (c : E) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range F.e)) :
    F.coefX (c • x) a = c * F.coefX x a := by
  have hcx : c • x ∈ Submodule.span E (Set.range F.e) := Submodule.smul_mem _ c hx
  unfold Formalism.MainNotions.S.FlagG.coefX
  rw [dite_eq_left hx, dite_eq_left hcx]
  have hprod : (⟨c • x, hcx⟩ : Submodule.span E (Set.range F.e)) = c • ⟨x, hx⟩ := rfl
  rw [hprod, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Ia_fg_and_mem_iff {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ)
    (T : E) (F : Formalism.MainNotions.S.FlagG S r T) (Λ : Submodule (𝓞 E) S.V) (a : Fin r) (hΛ : Λ.FG) :
    (GlobalTheory.RowLatXS.Ia Λ F a).FG ∧ ∀ t : E, t ∈ GlobalTheory.RowLatXS.Ia Λ F a ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
  classical
  have hXle : F.Xa (a.val + 1) ≤ Submodule.span E (Set.range F.e) := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.span_mono (Set.image_subset_range _ _)

  let W : Submodule (𝓞 E) S.V := Λ ⊓ (F.Xa (a.val + 1)).restrictScalars (𝓞 E)
  have hmem : ∀ x : W, (x : S.V) ∈ Submodule.span E (Set.range F.e) := fun x =>
    hXle ((Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 x.2).2)
  let g : W →ₗ[𝓞 E] E :=
    { toFun := fun x => F.coefX (x : S.V) a
      map_add' := fun x y => coefX_add_flag_measures F a (hmem x) (hmem y)
      map_smul' := fun c x => by
        change F.coefX (c • (x : S.V)) a = c • F.coefX (x : S.V) a
        rw [← algebraMap_smul E c (x : S.V), coefX_smul_flag_measures F a _ (hmem x), Algebra.smul_def] }
  have hrange : ∀ t : E, t ∈ LinearMap.range g ↔
      ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t := by
    intro t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (Submodule.mem_inf.1 x.2).1, (Submodule.mem_inf.1 x.2).2, rfl⟩
    · rintro ⟨x, hx, hxa, rfl⟩
      exact ⟨⟨x, Submodule.mem_inf.2 ⟨hx, hxa⟩⟩, rfl⟩

  have hIa : GlobalTheory.RowLatXS.Ia Λ F a = LinearMap.range g := by
    unfold GlobalTheory.RowLatXS.Ia
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hrange t).2 ht
    · intro t ht
      exact Submodule.subset_span ((hrange t).1 ht)
  refine ⟨?_, fun t => by rw [hIa]; exact hrange t⟩

  have : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  have : IsNoetherian (𝓞 E) W := isNoetherian_of_le inf_le_left
  rw [hIa, LinearMap.range_eq_map]
  exact (IsNoetherian.noetherian (⊤ : Submodule (𝓞 E) W)).map g

end GlobalTheory.RowLatXS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBound
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.FixIdx

section

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem idx_inf_le (A B C W : Submodule R V) (hAB : A ≤ B) (hAW : A ≤ W) (h : idx B C ≠ 0) :
    idx A (C ⊓ W) ≠ 0 ∧ idx A (C ⊓ W) ≤ idx B C := by
  have e : idx A (C ⊓ W) = idx A C := by
    unfold idx
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ W).toAddSubgroup, ← AddSubgroup.inf_relIndex_right C.toAddSubgroup]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hAW hx.2⟩, hx.2⟩⟩
  rw [e]
  have hle : A.toAddSubgroup ≤ B.toAddSubgroup := hAB
  exact ⟨fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    AddSubgroup.relIndex_le_of_le_right hle h⟩

theorem gens_of_sup (A C D : Submodule R V) (hD : A ⊓ C ≤ D) (hDA : D ≤ A) (e : ℕ) (t : Finset V)
    (ht : t.card ≤ e) (h : A ⊔ C = C ⊔ Submodule.span R (t : Set V)) :
    ∃ t' : Finset V, t'.card ≤ e ∧ A = D ⊔ Submodule.span R (t' : Set V) := by
  have h1 : ∀ x : V, ∃ a : V, x ∈ t → a ∈ A ∧ x - a ∈ C := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ A ⊔ C := by rw [h]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨a, fun _ => ⟨ha, by simpa using hc⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  have hsA : Submodule.span R ((t.image f : Finset V) : Set V) ≤ A := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact (hf x hx).1
  refine ⟨t.image f, Finset.card_image_le.trans ht, le_antisymm ?_ (sup_le hDA hsA)⟩
  have h2 : A ≤ C ⊔ Submodule.span R ((t.image f : Finset V) : Set V) := by
    refine le_trans (le_sup_left (b := C)) ?_
    rw [h]
    refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
    have : x = (x - f x) + f x := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (hf x hx).2
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)))
  intro x hx
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.1 (h2 hx)
  refine Submodule.add_mem_sup (hD ⟨?_, hc⟩) hs
  simpa using A.sub_mem hx (hsA hs)

end

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [StarRing K] in
theorem isLatMod_of_idx (A B : Submodule (𝓞 K) V) (S I : Submodule K V) (hA : IsLatMod A S I) (hBA : B ≤ A)
    (hI : rs (𝓞 K) I ≤ B) (h : idx A B ≠ 0) : IsLatMod B S I := by
  obtain ⟨⟨M, hM, hL⟩, hsp⟩ := hA
  refine ⟨⟨B ⊓ M, ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M := isNoetherian_of_fg_of_noetherian _ hM
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 hBA).symm
  · rw [← hsp]; exact Submodule.span_mono hBA
  · rw [← hsp, Submodule.span_le]
    intro x hx
    have h1 : (idx A B) • x ∈ B := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup) hx
    have h2 : ((idx A B : K))⁻¹ • ((idx A B) • x) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 h), one_smul] at h2

variable [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem radical (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) :
    II N.F N.F' ≤ wSp N.F N.F' ∧
      ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
  obtain ⟨-, -, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    rw [← H.herm, (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1)),
      star_zero]
  rw [hw]
  refine ⟨le_sup_right, fun x hx => ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩⟩
  obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
  have haa := hx0 a (Submodule.mem_sup_left ha)
  rw [map_add (f := _), LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ha0 : a = 0 := by
    by_contra hne
    have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
    have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
    rw [e, haa] at this
    simp at this
  rw [ha0, zero_add]; exact hi

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧ 0 < N.gI g Λ ∧ 0 < N.iI g Λ ∧ (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del ∧ ((N.gI g Λ : ℝ) * N.iI g Λ ≤ N.Del) ∧ GenBy (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K)) N.j ∧ del H (latTh N.F N.F' Λ) = (N.gI g Λ : ℝ) * N.iI g Λ * N.NT ∧ IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨hb0, -, hDel, hbar⟩ := _root_.GlobalTheory.DegCnt.SplitIdx.main K V H hK r N g Λ hg hΛ
  obtain ⟨hnB, -, h1L, hB, t, ht, hgen⟩ := _root_.GlobalTheory.DegCnt.InnerIndex.main K V H hK r N g Λ hg hΛ
  obtain ⟨hd0, -, -, hlat0, -⟩ := _root_.GlobalTheory.DegCnt.PrimPerp.main K V H hK r N g Λ hg hΛ
  obtain ⟨hIW, hrad⟩ := radical hK N
  have hww : wSp N.F' N.F = wSp N.F N.F' := by
    unfold wSp V0
    rw [sup_comm N.F'.X, Set.pair_comm]
  have hn0 : idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, zero_mul] at hnB
    linarith
  have hB0 : cardB N.F N.F' Λ ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, mul_zero] at hnB
    linarith
  have hThLa : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) := by
    intro x hx
    refine ⟨⟨⟨(h1L hx.1).2, by rw [hww]; exact hx.2⟩, ⟨(h1L hx.1).1, hx.2⟩⟩, ?_⟩
    obtain ⟨l, hl, i, hi, rfl⟩ := Submodule.mem_sup.1 hx.1.1
    refine Submodule.mem_sup.2 ⟨(l, l), ⟨⟨hl.1, hl.1⟩, ?_⟩, (i, i), ⟨hi.2, hi.1⟩, rfl⟩
    simp
  have hLa0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hLaL : latLa N.F N.F' Λ (g : 𝓞 K) ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ :=
    fun x hx => ⟨hx.1.2.1, hx.1.1.1⟩
  have hmul : N.iI g Λ * N.gI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ hThLa hLa0
  obtain ⟨hp0, hpn⟩ : idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≠ 0 ∧
      idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) :=
    idx_inf_le _ _ _ _ inf_le_left inf_le_right hn0
  have hq0 : idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≠ 0 := fun h0 =>
    hn0 (AddSubgroup.relIndex_eq_zero_of_le_right
      (show (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ).toAddSubgroup ≤ (latL N.F N.F' Λ).toAddSubgroup from
        fun x hx => hx.1) h0)
  have hiB : N.iI g Λ ≤ cardB N.F N.F' Λ :=
    (idx_inf_le _ _ _ (rs (𝓞 K) (wSp N.F N.F')) hLaL (hLa0.trans inf_le_right) hq0).2.trans hB
  have hi0 : N.iI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, zero_mul])
  have hg0 : N.gI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, mul_zero])
  have hmulR : (N.gI g Λ : ℝ) * N.iI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) := by
    rw [← hmul]; push_cast; ring
  have hmain : (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del := by
    rw [← hDel, ← hnB, sq (N.iI g Λ : ℝ), ← mul_assoc, hmulR]
    have e1 : (idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) : ℝ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) := by
      exact_mod_cast hpn
    have e2 : (N.iI g Λ : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast hiB
    gcongr
  have hITh : rs (𝓞 K) (II N.F N.F') ≤ latTh N.F N.F' Λ := by
    intro x hx
    refine ⟨⟨Submodule.mem_sup_right hx, ?_⟩, hIW hx⟩
    exact (mem_perp_iff H _ x).2 fun y hy => (mem_perp_iff H _ x).1 (hIW hx) y (Submodule.mem_sup_left hy)
  have hlat : IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') :=
    isLatMod_of_idx _ _ _ _ hlat0 (hThLa.trans hLa0) hITh hp0
  refine ⟨hThLa, Nat.pos_of_ne_zero hg0, Nat.pos_of_ne_zero hi0, hmain, le_trans ?_ hmain, ?_, ?_, hlat⟩
  · have e1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi0
    have e2 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    calc (N.gI g Λ : ℝ) * N.iI g Λ = (N.gI g Λ : ℝ) * (N.iI g Λ * 1) * 1 ^ 2 := by ring
      _ ≤ (N.gI g Λ : ℝ) * (N.iI g Λ * N.iI g Λ) * (N.bI Λ : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  · have h1 : lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ := h1L.trans inf_le_left
    obtain ⟨t', ht', h'⟩ := ((GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ h1 hn0).2 N.j t ht hgen).2
      (flagPairDefinitePartLattice N.F N.F' Λ ⊔ lamOne N.F N.F' Λ) le_sup_right (sup_le inf_le_left h1)
    exact gens_of_sup _ _ _
      (le_trans (show flagPairDefinitePartLattice N.F N.F' Λ ⊓ lamOne N.F N.F' Λ ≤ latTh N.F N.F' Λ from
        fun x hx => ⟨hx.2, hx.1.2⟩) hThLa) hLa0 N.j t' ht' h'
  · rw [(DelScale.main K V H hK _ _ _ _ hIW hrad hlat0 hlat).2.2.1, hd0, hmulR]
    have : idx (latTh N.F N.F' Λ) (flagPairDefinitePartLattice N.F N.F' Λ) = 1 :=
      AddSubgroup.relIndex_eq_one.2 (hThLa.trans hLa0)
    rw [gidx, this]
    simp

end GlobalTheory.DegCnt.FixIdx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcParamEqWeightStepZeroAddRho
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem hcParam_eq_weight_step_zero_add_rho : ∀ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), (((D.hcW u τ).u i : ℚ) : ℝ) = ((Formalism.L2.Forms.lamT u 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℝ) + ((rhoVec D.R.k i : ℚ) : ℝ) := by
  intro D u τ i
  rw [Formalism.L2.Forms.lamT_zero]
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)
  rw [dite_eq_left (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)] at h0
  have hq : ((D.hcW u τ).u i : ℚ) =
      (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i := by
    rw [h0, hcToWeightQ]
    simp
  rw [hq]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevel
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem selfDualAt_of_tLat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J _ _ T f L hL v hv
  obtain ⟨⟨hfin, _⟩, hint, hT, _, _⟩ := hL
  exact self_dual_local F E n cm.sig J v L T hfin (fun x hx y hy => hint y hy x hx)
    (fun y hy => hT y hy) hv

end GlobalTheory.St.G
end

