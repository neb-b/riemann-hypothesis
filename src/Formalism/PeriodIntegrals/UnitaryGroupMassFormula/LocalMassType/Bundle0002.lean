module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def K1 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) : Set (HA (Fv F v) σ J) :=
  {k | k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧ ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
    locF v (k • ratTup (Fv F v) (F0 P)) a - locF v (ratTup (Fv F v) (F0 P)) a =
      sc (E := E) v (g : Fv F v) • y}

def UOg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2 * (g : Fv F v)⁻¹) * x p ∈ OEv (E := E) v}

def stabilizerCompact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) : Set (S0 (Fv F v) σ J P) :=
  Subtype.val ⁻¹' Formalism.L2.SG.TypedSets.Kv σ J Λ v

theorem stabilizer_compact_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) :
    LocMassOrdW.stabilizerConjugateCompact σ J v P Λ 1 = stabilizerCompact σ J v Λ P := by
  ext h
  simp [LocMassOrdW.stabilizerConjugateCompact, stabilizerCompact]

theorem KSv_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) :
    KSvT σ J v P Λ 1 = KSv σ J v P Λ := by
  ext s
  simp [KSvT, KSv]

def StepOm : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')),
    StdHyp σ J ψ → P.IsStd σ J T → P'.IsStd σ J T' → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g → etaV (E := E) v = 1 →
    κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v →
    (∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a =
        sc (E := E) v (g : Fv F v) • y) →
    μG.IsHaarMeasure →
    μS0.IsHaarMeasure → IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) →
    μS0'.IsHaarMeasure → IsCompatLoc σ J v (F0 P') μG μS0' (omAt σ J ψ v (TFl σ J v P')) →
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) →
    LocMassOrdW.IsLatLoc v Λ →
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 → (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0 →
    Mv σ J ψ v (TFl σ J v P) (TFl σ J v P') (OmTyp v Λ g r) *
        ((μS0 (stabilizerCompact σ J v Λ P)).toReal * (μS0' (stabilizerCompact σ J v Λ P')).toReal) =
      (μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v)).toReal * (μG (K1 σ J v Λ g P)).toReal

def StepU : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ),
    StdHyp σ J ψ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    volU (E := E) ψ v (deepCongruenceVolume v g r) =
      (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal * (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal

def StepIdx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μG : Measure (HA (Fv F v) σ J)) (μS0 : Measure (S0 (Fv F v) σ J P)),
    StdHyp σ J ψ → P.IsStd σ J T → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g → etaV (E := E) v = 1 →
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → μG.IsHaarMeasure → LocMassOrdW.IsLatLoc v Λ →
    μS0.IsHaarMeasure → (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 →
    (μG (Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v)).toReal *
        (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal =
      (μG (K1 σ J v Λ g P)).toReal * (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal

def StepPos : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ),
    StdHyp σ J ψ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal ≠ 0 →
      (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal ≠ 0

theorem arith (M a a' k k1 kn s s' u ug : ℝ) (hM : M * (a * a') = k * k1) (hs : s = a * u)
    (hs' : s' = a' * u) (hidx : kn * ug = k1 * u) (ha : a ≠ 0) (ha' : a' ≠ 0) (hug : u ≠ 0 → ug ≠ 0) :
    M / (u * ug) = k * kn / (s * s') := by
  subst hs hs'
  by_cases hu : u = 0
  · subst hu
    simp
  · have hug' := hug hu
    rw [div_eq_div_iff (mul_ne_zero hu hug') (mul_ne_zero (mul_ne_zero ha hu) (mul_ne_zero ha' hu))]
    linear_combination (u * u) * hM - (k * u) * hidx

end PI.LocMassTypW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalLatticeOfGlobal
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.LocMassTypW

def LatOfGlob : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E)),
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    LocMassOrdW.IsLatLoc v Λ

end PI.LocMassTypW

namespace PI.LocMassTypL

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

theorem ratV_add (x y : Fin n → E) : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV, map_add (f := _)]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i; simp [ratV]

theorem ratV_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    ratV (F := F) R (∑ i ∈ s, x i) = ∑ i ∈ s, ratV (F := F) R (x i) := by
  funext j; simp [ratV, map_sum, Finset.sum_apply]

theorem ratV_zsmul (m : ℤ) (x : Fin n → E) : ratV (F := F) R (m • x) = m • ratV (F := F) R x := by
  funext i; simp [ratV, map_zsmul]

theorem ratV_smul (a : E) (x : Fin n → E) :
    ratV (F := F) R (a • x) = inclR (F := F) R a • ratV (F := F) R x := by
  funext i; simp [ratV, map_mul]

end Rat

theorem local_lattice_of_global : PI.LocMassTypW.LatOfGlob := by
  intro F E _ _ _ _ _ v n Λ hL
  obtain ⟨L, hL, hLΛ⟩ := hL
  classical
  obtain ⟨S, hS⟩ := hL.toIsLattice.fg
  let b := NumberField.RingOfIntegers.basis E
  set T : Set (Fin n → E) := Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × S =>
    (b p.1 : 𝓞 E) • (p.2 : Fin n → E)) with hT
  have hTfin : T.Finite := Set.finite_range _
  have hTL : T ⊆ (L : Set (Fin n → E)) := by
    rintro _ ⟨⟨j, s⟩, rfl⟩
    exact L.smul_mem _ (hS ▸ Submodule.subset_span (Finset.mem_coe.2 s.2))
  have key : ∀ x ∈ L, ratV (F := F) (Fv F v) x ∈
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).1 hx
    rw [ratV_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    rw [← b.sum_repr (f s), Finset.sum_smul, ratV_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_assoc, ratV_zsmul]
    have hmem : ratV (F := F) (Fv F v) ((b j : 𝓞 E) • s) ∈ ratV (F := F) (Fv F v) '' T :=
      ⟨_, ⟨(j, ⟨s, hs⟩), rfl⟩, rfl⟩
    exact zsmul_mem (Submodule.subset_span hmem) _
  have heq : latLoc (E := E) v Λ =
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    apply le_antisymm
    · rw [latLoc, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hLΛ] at hx
      exact key x hx
    · rw [latLoc]
      exact Submodule.span_mono (Set.image_mono (by rw [← hLΛ]; exact hTL))
  refine ⟨?_, ?_⟩
  · rw [heq]; exact Submodule.fg_span (hTfin.image _)
  · have hspan : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        ratV (F := F) (Fv F v) x ∈ Submodule.span (Fv F v ⊗[F] E)
          (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        show ratV (F := F) (Fv F v) y ∈ latLoc (E := E) v Λ
        exact Submodule.subset_span ⟨y, hLΛ ▸ hy, rfl⟩
      | zero => rw [ratV_zero]; exact Submodule.zero_mem _
      | add y z _ _ h1 h2 => rw [ratV_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h => rw [ratV_smul]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hspan (fun j => if i = j then (1 : E) else 0) (by simp [hL.span_eq_top])
    convert this using 1
    funext j
    by_cases hij : i = j <;> simp [ratV, hij]

end PI.LocMassTypL
end
end

