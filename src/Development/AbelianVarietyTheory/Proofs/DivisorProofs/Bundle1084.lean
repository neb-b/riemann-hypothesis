module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtension
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory

theorem selfDual_orthogonal_unit_step : ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
    [FiniteDimensional K.E V] (h : V → V → K.E), (∀ y y' z, h (y + y') z = h y z + h y' z) →
    (∀ (a : K.E) y z, h (a • y) z = a * h y z) → (∀ y z, h z y = K.c (h y z)) →
    ∀ L : Submodule K.O V, L.FG → Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∀ (k : ℕ) (f : Fin k → V), (∀ i, f i ∈ L) → (∀ i j, i ≠ j → h (f i) (f j) = 0) →
    (∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t) → k < Module.finrank K.E V →
    ∃ y ∈ L, (∀ i, h y (f i) = 0) ∧ ∃ t : K.O, IsUnit t ∧ h y y = algebraMap K.O K.E t := by
  intro K V _ _ _ _ _ h hadd hsmul hsym L hLfg hLspan hdual k f hfL horth hunit hk
  have alg_inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hadd2 : ∀ y z z', h y (z + z') = h y z + h y z' := by
    intro y z z'
    rw [hsym (z + z') y, hadd, map_add (f := _), ← hsym, ← hsym]
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym (a • z) y, hsmul, map_mul, ← hsym]
  let H1 : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z,
      map_smul' := fun a y => by simp [hsmul] }
  let H2 : V → V →+ K.E := fun y => AddMonoidHom.mk' (fun z => h y z) (hadd2 y)
  have h0l : ∀ z, h 0 z = 0 := fun z => (H1 z).map_zero
  have hsub1 : ∀ a b z, h (a - b) z = h a z - h b z := fun a b z => (H1 z).map_sub a b
  have hsub2 : ∀ y a b, h y (a - b) = h y a - h y b := fun y a b => (H2 y).map_sub a b
  have hsum1 : ∀ (g : Fin k → V) z, h (∑ i, g i) z = ∑ i, h (g i) z :=
    fun g z => map_sum (H1 z) g Finset.univ
  have hsum2 : ∀ (g : Fin k → V) y, h y (∑ i, g i) = ∑ i, h y (g i) :=
    fun g y => map_sum (H2 y) g Finset.univ
  have hsmulO : ∀ (o : K.O) (v : V), (algebraMap K.O K.E o) • v = o • v :=
    fun o v => algebraMap_smul K.E o v
  have hint : ∀ y ∈ L, ∀ z ∈ L, ∃ a : K.O, h y z = algebraMap K.O K.E a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    exact ⟨a, ha.symm⟩
  have hs : ∀ i, h (f i) (f i) ≠ 0 := by
    intro i
    obtain ⟨t, ht, he⟩ := hunit i
    rw [he]
    intro h0
    apply ht.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  let M : Submodule K.O V :=
    { carrier := {y | y ∈ L ∧ ∀ i, h y (f i) = 0}
      add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, fun i => by rw [hadd, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, fun i => h0l (f i)⟩
      smul_mem' := fun o y hy => ⟨L.smul_mem o hy.1, fun i => by rw [← hsmulO, hsmul, hy.2 i, mul_zero]⟩ }
  have memM : ∀ y, y ∈ M ↔ y ∈ L ∧ ∀ i, h y (f i) = 0 := fun y => Iff.rfl

  have hP : ∀ l ∈ L, ∃ p ∈ M, (∀ w, (∀ i, h w (f i) = 0) → h w l = h w p) ∧
      (l ∉ Submodule.span K.E (Set.range f) → p ≠ 0) := by
    intro l hl
    set g : Fin k → V := fun i => (h l (f i) / h (f i) (f i)) • f i with hg
    have hgL : ∀ i, g i ∈ L := by
      intro i
      obtain ⟨a, ha⟩ := hint l hl (f i) (hfL i)
      obtain ⟨t, ht, he⟩ := hunit i
      have hc : h l (f i) / h (f i) (f i) = algebraMap K.O K.E (a * ↑ht.unit⁻¹) := by
        rw [ha, he, map_mul, div_eq_mul_inv]
        congr 1
        exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
      simp only [hg]
      rw [hc, hsmulO]
      exact L.smul_mem _ (hfL i)
    refine ⟨l - ∑ i, g i, (memM _).2 ⟨L.sub_mem hl (L.sum_mem fun i _ => hgL i), fun j => ?_⟩,
      fun w hw => ?_, fun hn h0 => ?_⟩
    · rw [hsub1, hsum1, Finset.sum_eq_single j]
      · simp only [hg, hsmul]
        rw [div_mul_cancel₀ _ (hs j), sub_self]
      · intro i _ hij
        simp only [hg, hsmul, horth i j hij, mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · rw [hsub2, hsum2, Finset.sum_eq_zero, sub_zero]
      intro i _
      simp only [hg, hsmul2, hw i, mul_zero]
    · apply hn
      rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hspan : Submodule.span K.E (Set.range f) ≠ ⊤ := by
    intro htop
    have h1 := finrank_range_le_card (R := K.E) f
    rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
    omega
  obtain ⟨l, hl, hlnot⟩ : ∃ l ∈ L, l ∉ Submodule.span K.E (Set.range f) := by
    by_contra hcon
    push_neg at hcon
    apply hspan
    rw [eq_top_iff, ← hLspan]
    exact Submodule.span_le.2 (fun x hx => hcon x hx)
  have hMne : M ≠ ⊥ := by
    obtain ⟨p, hpM, -, hp0⟩ := hP l hl
    intro hb
    rw [hb] at hpM
    exact hp0 hlnot ((Submodule.mem_bot _).1 hpM)

  by_contra hno
  push_neg at hno
  let Q : Submodule K.O K.E := Submodule.map (Algebra.linearMap K.O K.E) (IsLocalRing.maximalIdeal K.O)
  have hQsmul : ∀ (o : K.O) x, x ∈ Q → algebraMap K.O K.E o * x ∈ Q := by
    intro o x hx
    rw [← Algebra.smul_def]
    exact Q.smul_mem o hx
  have hQdiag : ∀ y ∈ M, h y y ∈ Q := by
    intro y hy
    obtain ⟨t, ht⟩ := hint y hy.1 y hy.1
    refine Submodule.mem_map.2 ⟨t, ?_, by rw [Algebra.linearMap_apply, ht]⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hno y hy.1 hy.2 t hu ht
  have hpol : ∀ y ∈ M, ∀ z ∈ M, ∀ o : K.O,
      algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z ∈ Q := by
    intro y hy z hz o
    obtain ⟨μ, hμ⟩ := K.c_int o
    have hw : y + (algebraMap K.O K.E o) • z ∈ M := by
      rw [hsmulO]
      exact M.add_mem hy (M.smul_mem o hz)
    have e : algebraMap K.O K.E o * h z y + K.c (algebraMap K.O K.E o) * h y z =
        h (y + (algebraMap K.O K.E o) • z) (y + (algebraMap K.O K.E o) • z) - h y y
          - algebraMap K.O K.E o * (algebraMap K.O K.E μ * h z z) := by
      simp only [hadd, hadd2, hsmul, hsmul2, hμ]
      ring
    rw [e]
    exact Q.sub_mem (Q.sub_mem (hQdiag _ hw) (hQdiag _ hy)) (hQsmul _ _ (hQsmul _ _ (hQdiag _ hz)))
  have hQall : ∀ y ∈ M, ∀ z ∈ M, h y z ∈ Q := by
    intro y hy z hz
    obtain ⟨a, b, hab, hnot⟩ := K.c_res
    have h1 := hpol y hy z hz 1
    have h2 := hpol y hy z hz a
    simp only [map_one, one_mul] at h1
    rw [hab] at h2
    have h3 : algebraMap K.O K.E (a - b) * h y z ∈ Q := by
      have := Q.sub_mem (hQsmul a _ h1) h2
      convert this using 1
      rw [map_sub]
      ring
    obtain ⟨e, he⟩ := hint y hy.1 z hz.1
    rw [he, ← map_mul] at h3
    obtain ⟨m', hm', hm'e⟩ := Submodule.mem_map.1 h3
    rw [Algebra.linearMap_apply] at hm'e
    have hme := alg_inj hm'e
    rw [hme] at hm'
    rw [he]
    exact Submodule.mem_map.2 ⟨e,
      ((IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hm').resolve_left hnot, rfl⟩

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπm : IsLocalRing.maximalIdeal K.O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπmem : π ∈ IsLocalRing.maximalIdeal K.O := by
    rw [hπm]; exact Ideal.mem_span_singleton_self π
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply alg_inj
    rw [h0, map_zero]
  have hle : M ≤ IsLocalRing.maximalIdeal K.O • M := by
    intro w hw
    have hw' : (algebraMap K.O K.E π)⁻¹ • w ∈ M := by
      refine (memM _).2 ⟨(hdual _).2 fun l hl => ?_, fun i => by rw [hsmul, hw.2 i, mul_zero]⟩
      obtain ⟨p, hp, hpw, -⟩ := hP l hl
      rw [hsmul, hpw w hw.2]
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 (hQall w hw p hp)
      rw [hπm, Ideal.mem_span_singleton'] at hb
      obtain ⟨d, rfl⟩ := hb
      rw [← hbe, Algebra.linearMap_apply, map_mul]
      exact ⟨d, by field_simp⟩
    have hweq : w = π • ((algebraMap K.O K.E π)⁻¹ • w) := by
      rw [← hsmulO, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
    rw [hweq]
    exact Submodule.smul_mem_smul hπmem hw'
  have hfg : M.FG := Submodule.FG.of_le hLfg (fun y hy => hy.1)
  exact hMne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle
    (IsLocalRing.maximalIdeal_le_jacobson _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependent
section
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegral
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.GramUnit

theorem isReduced_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (P : F[X]) (hP : P.Separable) (hu : aeval u P = 0) (hadj : Algebra.adjoin F {u} = ⊤) :
    IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨N, hN⟩ := hx
  have hxmem : x ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have hdvdP : minpoly F u ∣ P := minpoly.dvd F u hu
  have hsq : Squarefree (minpoly F u) := (hP.of_dvd hdvdP).squarefree
  have hfN : minpoly F u ∣ f ^ N := minpoly.dvd F u (by rw [map_pow]; exact hN)
  obtain ⟨g, hg⟩ := hsq.isRadical N f hfN
  subst hg
  change aeval u (minpoly F u * g) = 0
  rw [map_mul, minpoly.aeval, zero_mul]

theorem eq_zero_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    [IsReduced A] (x : A) (h : ∀ z, Algebra.trace F A (x * z) = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7; revert F A h_2 h_3 h_4 h_5 h_6 h_7 x h; exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp)
  | exact @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp
  | (apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceMulVanishing.trace_mul_eq_zero_imp ..)

theorem det_gram_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) [IsReduced B.A] {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (hβ : IsUnit β) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set y := ∑ i, v i • b i with hy
  have hlin : ∀ z, B.herm β y z = ∑ i, v i * B.herm β (b i) z := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.UnitLemma.InvAlg.herm, hy, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hj : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    rw [hlin]
    have := congrFun hv j
    simpa [Matrix.vecMul, dotProduct] using this
  have hsemi : ∀ (d : K.E) (a : B.A), B.σ (d • a) = K.c d • B.σ a := by
    intro d a
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hall : ∀ z, Algebra.trace K.E B.A (β * y * z) = 0 := by
    intro z
    have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hsemi]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    have := hj j
    simp only [GlobalTheory.UnitLemma.InvAlg.herm] at this
    rw [this, mul_zero]
  have hβy : β * y = 0 := eq_zero_of_trace_mul (β * y) hall
  have hy0 : y = 0 := by
    obtain ⟨u, rfl⟩ := hβ
    have := congrArg (fun t => ((u⁻¹ : B.Aˣ) : B.A) * t) hβy
    simpa [← mul_assoc] using this
  exact hv0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hy0))

end GlobalTheory.TwLat.GramUnit


open GlobalTheory.TwLat.GramUnit in
theorem GlobalTheory.TwLat.isUnit_gram_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (P : K.E[X]), P.Separable → aeval u P = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β : B.A, IsUnit β → IsUnit (GlobalTheory.TwLat.gram e b β) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b u P hP hu hadj β hβ
  haveI : IsReduced B.A := isReduced_of_adjoin u P hP hu hadj
  have hd := det_gram_ne_zero B b β hβ
  have hmap : GlobalTheory.TwLat.gram e b β = (Matrix.of fun i j => B.herm β (b i) (b j)).map e := by
    ext i j; rfl
  rw [hmap, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have := RingHom.map_det (e : K.E →+* w.adicCompletion E) (Matrix.of fun i j => B.herm β (b i) (b j))
  rw [show ((Matrix.of fun i j => B.herm β (b i) (b j)).map e) =
    (e : K.E →+* w.adicCompletion E).mapMatrix (Matrix.of fun i j => B.herm β (b i) (b j)) from rfl, ← this]
  exact (map_ne_zero_iff _ e.injective).mpr hd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StConstHolds
section
open MeasureTheory MvPolynomial GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3

theorem stConst_holds : StConst := by
  intro ι _ G hG
  obtain ⟨hsmooth, hzero, hnonneg, hpos⟩ := hG
  set N := Fintype.card ι
  set f : ℝ → ℝ := iteratedDeriv N G with hf

  have hf0 : ∀ x : ℝ, 1 < x → f x = 0 := by
    intro x hx
    have hev : G =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hzero y (le_of_lt hy)
    rw [hf, Filter.EventuallyEq.iteratedDeriv_eq N hev]
    simp
  have hfc : Continuous f := hsmooth.continuous_iteratedDeriv N (by exact_mod_cast le_top)
  set F : (ι → ℂ) → ℝ := fun w => f (∑ x, ‖w x‖ ^ 2) with hF
  have hFc : Continuous F := by
    apply hfc.comp
    fun_prop
  have hFs : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 1)
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    have : ∃ x, 1 < ‖w x‖ := by
      by_contra h
      push_neg at h
      exact absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 h) (not_le.2 hw)
    obtain ⟨x, hx⟩ := this
    apply hf0
    calc (1 : ℝ) < ‖w x‖ ^ 2 := by nlinarith
      _ ≤ ∑ y, ‖w y‖ ^ 2 :=
        Finset.single_le_sum (f := fun y => ‖w y‖ ^ 2) (fun y _ => by positivity) (Finset.mem_univ x)
  have hFn : 0 ≤ F := fun w => hnonneg _
  have hF0 : F 0 ≠ 0 := by
    simp only [hF, Pi.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact ne_of_gt hpos
  exact ne_of_gt (hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero hFs hFn hF0)

end GlobalTheory.PsCo.Pc3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StR
section
namespace GlobalTheory.PsCo.Pc3

theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := _root_.GlobalTheory.offDiagBlockNorm_cont_inv n ε
  exact ⟨hcont, hinv, _root_.GlobalTheory.offDiag_zero_iff_mem_K n ε, _root_.GlobalTheory.isCompact_offDiag_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibresStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.torsion_sections_exhaust_geometric_fibres : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  first | exact @GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | exact GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | (intros; apply GlobalTheory.Poinc.Tors.torsion_exhaust_geometric <;> assumption)
end

