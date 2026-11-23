module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0002
public import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaSummable
public import Formalism.HermitianLattices.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003
public import Lemmata.GeneralBFactSecondRest.Imports

@[expose] public section

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
section
open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section AutFiniteSec

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

lemma autFinite_short (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] (R : ℚ) :
    Set.Finite {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R} := by
  have hs := thetaSummable_main h hpos L 0 Complex.I (by simp)
  have hnorm : ∀ x : L, ‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + (x : V)) (0 + (x : V))) : ℚ) : ℂ))‖ =
        Real.exp (-Real.pi * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)) := by
    intro x
    rw [Complex.norm_exp, zero_add]
    congr 1
    have e : (Real.pi : ℂ) * Complex.I * Complex.I = -(Real.pi : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rw [e]
    simp
  have hev := (tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually
    (gt_mem_nhds (Real.exp_pos (-Real.pi * (R : ℝ))))
  rw [Filter.eventually_cofinite] at hev
  refine (hev.image Subtype.val).subset ?_
  rintro v ⟨hvL, hvR⟩
  refine ⟨⟨v, hvL⟩, ?_, rfl⟩
  show ¬ (‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + v) (0 + v)) : ℚ) : ℂ))‖ < Real.exp (-Real.pi * (R : ℝ)))
  rw [not_lt, hnorm ⟨v, hvL⟩]
  apply Real.exp_le_exp.2
  have hR : ((Algebra.trace ℚ K (h v v) : ℚ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvR
  nlinarith [Real.pi_pos]

end AutFiniteSec

theorem autFinite (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (_hsymm : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) :
    Set.Finite {g : V ≃ₗ[K] V | g ∈ isom h ∧ gmap g L = L} := by
  let : Submodule.IsFullLattice K L := hL
  obtain ⟨S, hS⟩ := Submodule.IsLattice.fg (A := K) (M := L)
  set R : ℚ := ∑ s ∈ S, Algebra.trace ℚ K (h s s) with hR
  have hSL : ∀ s ∈ S, s ∈ L := fun s hs => hS ▸ Submodule.subset_span hs
  have hsR : ∀ s ∈ S, Algebra.trace ℚ K (h s s) ≤ R := fun s hs =>
    Finset.single_le_sum (f := fun s => Algebra.trace ℚ K (h s s))
      (fun x _ => thetaSummable_nonneg h hpos x) hs
  have hT := autFinite_short h hpos L R
  have hspan : Submodule.span K (S : Set V) = ⊤ := by
    rw [eq_top_iff, ← Submodule.IsFullLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (NumberField.RingOfIntegers K) K (S : Set V) hx
  let Φ : (V ≃ₗ[K] V) → (S → V) := fun g s => g s
  apply Set.Finite.of_finite_image (f := Φ)
  · refine (Set.Finite.pi (t := fun _ : S => {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R})
      (fun _ => hT)).subset ?_
    rintro _ ⟨g, ⟨hg, hgL⟩, rfl⟩ s _
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    refine ⟨?_, ?_⟩
    · have hm : g s ∈ Formalism.HermitianLatticesTheory.gmap g L := Submodule.mem_map_of_mem (hSL s s.2)
      rwa [hgL] at hm
    · show Algebra.trace ℚ K (h (g s) (g s)) ≤ R
      rw [hg']
      exact hsR s s.2
  · intro g₁ _ g₂ _ hg
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    intro x hx
    exact congrFun hg ⟨x, hx⟩

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale
section
open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusScale_span (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (s : Set V)
    (hs : ∀ a ∈ s, ∀ b ∈ s, c * h a b ∈ (1 : Submodule R K)) :
    ∀ x ∈ Submodule.span R s, ∀ y ∈ Submodule.span R s, c * h x y ∈ (1 : Submodule R K) := by
  have key : ∀ a ∈ s, ∀ y ∈ Submodule.span R s, c * h a y ∈ (1 : Submodule R K) := by
    intro a ha y hy
    induction hy using Submodule.span_induction with
    | mem b hb => exact hs a ha b hb
    | zero => simp
    | add u w _ _ hu hw =>
        rw [map_add (f := _), mul_add]
        exact add_mem hu hw
    | smul r u _ hu =>
        rw [genusBasic_hsmul_right, mul_left_comm]
        exact genusBasic_mem_one_mul _ hu r
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem a ha => exact key a ha y hy
  | zero => simp
  | add u w _ _ hu hw =>
      rw [map_add (f := _), LinearMap.add_apply, mul_add]
      exact add_mem hu hw
  | smul r u _ hu =>
      rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
      exact genusBasic_mem_one_mul _ hu _

theorem genusScale_transfer (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : ∀ x ∈ L, ∀ y ∈ L, c * h x y ∈ (1 : Submodule R K)) :
    ∀ x ∈ M, ∀ y ∈ M, c * h x y ∈ (1 : Submodule R K) := by
  intro x hx y hy
  refine genusBasic_lg (K := K) (1 : Submodule R K) (c * h x y) ?_
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hxM : x ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hx
  have hyM : y ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hy
  rw [← hgL, isomAct_mem_gmap] at hxM hyM
  obtain ⟨s, hsS, hsx⟩ := locBasic_mem_locS.mp hxM
  obtain ⟨t, htS, hty⟩ := locBasic_mem_locS.mp hyM
  have hg' : ∀ u v : V, h (g u) (g v) = h u v := hg
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg' (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    exact e.symm
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  refine locBasic_mem_locS.mpr ⟨locBasic_sigma hinj hstar s * t,
    (hcompl (K := K) p).mul_mem (genusBasic_sigma_mem hinj hstar p s hsS) htS, ?_⟩
  have e : (locBasic_sigma hinj hstar s * t) • (c * h x y) =
      c * (algebraMap R K (locBasic_sigma hinj hstar s) * (algebraMap R K t * h x y)) := by
    rw [Algebra.smul_def, map_mul]
    ring
  rw [e]
  exact h1

end SlopeTestRemainingChoices

private theorem exists_nat_pos_mul_mem_one {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * z ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  have hw : IsIntegral ℤ ((y.natAbs : K) * z) := by
    rcases Int.natAbs_eq y with e | e
    · rw [← Int.cast_natCast, ← e, ← zsmul_eq_mul]
      exact hy
    · have e' : (y.natAbs : ℤ) = -y := by linarith
      rw [← Int.cast_natCast, e', Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy0, Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩⟩

theorem genusScale : GenusScale := by
  intro K V _ _ _ _ _ _ _ _ h _ L hL
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hr : IsIntegral ℤ (algebraMap (𝓞 K) K r) := NumberField.RingOfIntegers.isIntegral_coe r
    exact ⟨⟨star (algebraMap (𝓞 K) K r), hr.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  obtain ⟨s, hs⟩ := hL.fg
  choose n hn0 hn using exists_nat_pos_mul_mem_one (K := K)
  refine ⟨∏ q ∈ s ×ˢ s, n (h q.1 q.2), Finset.prod_pos (fun q _ => hn0 _), ?_⟩
  have hLd : ∀ x ∈ L, ∀ y ∈ L,
      ((∏ q ∈ s ×ˢ s, n (h q.1 q.2) : ℕ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← hs]
    refine genusScale_span hinj hstar h _ _ ?_
    intro a ha b hb
    have hmem : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
    obtain ⟨k, hk⟩ : n (h a b) ∣ ∏ q ∈ s ×ˢ s, n (h q.1 q.2) :=
      Finset.dvd_prod_of_mem (fun q : V × V => n (h q.1 q.2)) hmem
    rw [hk, Nat.cast_mul, mul_comm ((n (h a b) : ℕ) : K), mul_assoc]
    have hm := genusBasic_mem_one_mul _ (hn (h a b)) (k : 𝓞 K)
    rwa [map_natCast] at hm
  intro M hM x hx y hy
  exact genusScale_transfer hinj hstar h _ L M hM.2 hLd x hx y hy

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.MajBasic
section
open NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajBasicAux

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majBasic_majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = star (vecAt b v x) ⬝ᵥ ((((X v)⁻¹)ᴴ * (X v)⁻¹) *ᵥ vecAt b v y) := by
  unfold majAt
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

end MajBasicAux

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice
section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

end MajLatticeMain

end Formalism.HermitianLatticesTheory
end
end

