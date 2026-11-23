module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMergedModulePushoutsContainBoth
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.Pass.LocDirect

theorem pushSet_merge : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (a₁ : ℕ) (x₁ : Fin a₁ → D.nd.X i), (∀ j, x₁ j ∈ Xs) → ∀ (E₁ : Fin a₁ → Fin D.R.nV → KK D.nd i) (Y₁ : Submodule (D.nd.O i) (Fin a₁ → Fin D.R.nV → KK D.nd i)), Y₁.FG → ∀ (hst₁ : (∀ γ : GE D.nd, ∀ y ∈ Y₁, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (y j)) ∈ Y₁)) (hE₁ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j) ∈ Y₁)) (a₂ : ℕ) (x₂ : Fin a₂ → D.nd.X i), (∀ j, x₂ j ∈ Xs) → ∀ (E₂ : Fin a₂ → Fin D.R.nV → KK D.nd i) (Y₂ : Submodule (D.nd.O i) (Fin a₂ → Fin D.R.nV → KK D.nd i)), Y₂.FG → ∀ (hst₂ : (∀ γ : GE D.nd, ∀ y ∈ Y₂, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (y j)) ∈ Y₂)) (hE₂ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j) ∈ Y₂)), ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG) (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₁ E₁ Y₁ hst₁ hE₁ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE ∧ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₂ E₂ Y₂ hst₂ hE₂ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE := by
  intro D i w hw r Xs k M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
  set L₁ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₁ → Fin D.R.nV → KK D.nd i) :=
    LinearMap.funLeft _ _ (Fin.castAdd a₂) with hL₁
  set L₂ : (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) →ₗ[D.nd.O i] (Fin a₂ → Fin D.R.nV → KK D.nd i) :=
    LinearMap.funLeft _ _ (Fin.natAdd a₁) with hL₂
  set x : Fin (a₁ + a₂) → D.nd.X i := Fin.append x₁ x₂ with hx
  set E : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i := Fin.append E₁ E₂ with hEdef
  set Y : Submodule (D.nd.O i) (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) := Y₁.comap L₁ ⊓ Y₂.comap L₂ with hY
  have hL₁a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i),
      L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (L₁ v j) := by
    intro γ v; funext j; simp [hL₁, LinearMap.funLeft_apply, hx, Fin.append_left]
  have hL₂a : ∀ (γ : GE D.nd) (v : Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i),
      L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (v j)) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (L₂ v j) := by
    intro γ v; funext j; simp [hL₂, LinearMap.funLeft_apply, hx, Fin.append_right]
  have hL₁E : ∀ γ : GE D.nd,
      L₁ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j := by
    intro γ; funext j; simp [hL₁, LinearMap.funLeft_apply, hx, hEdef, Fin.append_left]
  have hL₂E : ∀ γ : GE D.nd,
      L₂ (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) =
        fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j := by
    intro γ; funext j; simp [hL₂, LinearMap.funLeft_apply, hx, hEdef, Fin.append_right]
  have hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y := by
    intro γ y hy
    refine ⟨?_, ?_⟩
    · show L₁ _ ∈ Y₁
      rw [hL₁a]; exact hst₁ γ _ hy.1
    · show L₂ _ ∈ Y₂
      rw [hL₂a]; exact hst₂ γ _ hy.2
  have hE : ∀ γ : GE D.nd,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y := by
    intro γ
    refine ⟨?_, ?_⟩
    · show L₁ _ ∈ Y₁
      rw [hL₁E]; exact hE₁ γ
    · show L₂ _ ∈ Y₂
      rw [hL₂E]; exact hE₂ γ
  have hFG : Y.FG := by
    let A : ((Fin a₁ → Fin D.R.nV → KK D.nd i) × (Fin a₂ → Fin D.R.nV → KK D.nd i)) →ₗ[D.nd.O i]
        (Fin (a₁ + a₂) → Fin D.R.nV → KK D.nd i) :=
      { toFun := fun p => Fin.append p.1 p.2
        map_add' := by
          intro p q; funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right]
        map_smul' := by
          intro c p; funext j
          refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [Fin.append_left, Fin.append_right] }
    have hYeq : Y = (Y₁.prod Y₂).map A := by
      ext y
      constructor
      · intro hy
        refine ⟨(L₁ y, L₂ y), ⟨hy.1, hy.2⟩, ?_⟩
        show Fin.append (L₁ y) (L₂ y) = y
        simp only [hL₁, hL₂, LinearMap.funLeft_apply]
        exact Fin.append_castAdd_natAdd
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · show L₁ (Fin.append p.1 p.2) ∈ Y₁
          have : L₁ (Fin.append p.1 p.2) = p.1 := by
            funext j; simp [hL₁, LinearMap.funLeft_apply, Fin.append_left]
          rw [this]; exact hp1
        · show L₂ (Fin.append p.1 p.2) ∈ Y₂
          have : L₂ (Fin.append p.1 p.2) = p.2 := by
            funext j; simp [hL₂, LinearMap.funLeft_apply, Fin.append_right]
          rw [this]; exact hp2
    rw [hYeq]
    exact (hY₁.prod hY₂).map A
  have hxs : ∀ j, x j ∈ Xs := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [hx, Fin.append_left]; exact hx₁ j
    · simp only [hx, Fin.append_right]; exact hx₂ j
  refine ⟨a₁ + a₂, x, hxs, E, Y, hFG, hst, hE, ?_, ?_⟩
  · rintro c ⟨φ₁, hφ₁, rfl⟩
    let ρ : ↥Y →ₗ[D.nd.O i] ↥Y₁ := L₁.restrict (p := Y) (q := Y₁) (fun y hy => hy.1)
    refine ⟨φ₁ ∘ₗ ρ, ?_, ?_⟩
    · intro γ y
      have h := hφ₁ γ (ρ y)
      simp only [LinearMap.comp_apply]
      rw [← h]
      congr 1
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₁a]
    · funext g
      simp only [LinearMap.comp_apply]
      congr 2
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₁E]
  · rintro c ⟨φ₂, hφ₂, rfl⟩
    let ρ : ↥Y →ₗ[D.nd.O i] ↥Y₂ := L₂.restrict (p := Y) (q := Y₂) (fun y hy => hy.2)
    refine ⟨φ₂ ∘ₗ ρ, ?_, ?_⟩
    · intro γ y
      have h := hφ₂ γ (ρ y)
      simp only [LinearMap.comp_apply]
      rw [← h]
      congr 1
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₂a]
    · funext g
      simp only [LinearMap.comp_apply]
      congr 2
      apply Subtype.ext
      simp [ρ, LinearMap.restrict_apply, hL₂E]

end GlobalTheory.Pass.LocDirect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.CoeffIdeal

theorem principal_of_saturated {S k : Type} [CommRing S] [IsNoetherianRing S] [CommRing k]
    [IsPrincipalIdealRing k] (π : S →+* k) (hπ : Function.Surjective π) (p : S)
    (hker : ∀ x, π x = 0 → p ∣ x) (hp : Ideal.span {p} ≤ Ideal.jacobson ⊥) (P : Ideal S)
    (hP : ∀ x, p * x ∈ P → x ∈ P) : ∃ g, P = Ideal.span {g} := by
  obtain ⟨g', hg'⟩ := (IsPrincipalIdealRing.principal (P.map π)).principal
  have h0 : g' ∈ P.map π := by rw [hg']; exact Submodule.mem_span_singleton_self _
  obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 h0
  refine ⟨g, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hg)⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian P) hp fun x hx => ?_
  have h1 : π x ∈ P.map π := Ideal.mem_map_of_mem π hx
  rw [hg'] at h1
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨c, rfl⟩ := hπ c'
  obtain ⟨y, hy⟩ := hker (x - c * g) (by rw [map_sub, map_mul, ← hc', smul_eq_mul, sub_self])
  have hyP : y ∈ P := hP y (hy ▸ P.sub_mem hx (P.mul_mem_left c hg))
  have e : x = c * g + p • y := by rw [smul_eq_mul, ← hy]; ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self g))
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hyP)

theorem c_frob_mem {S A : Type} [CommRing S] [IsNoetherianRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (hI : I ≤ Ideal.jacobson ⊥) (φ : S →+* S) (Φ : A →+* A)
    (hφ : ∀ a, s (φ a) = Φ (s a)) (hφI : I.map φ ≤ I) (x : A) (N : Ideal S) (hN : ∀ i, φ (TB.c i x) ∈ N)
    (j : ι) : TB.c j (Φ x) ∈ N := by
  have hH : IsHausdorff I (S ⧸ N) := IsHausdorff.of_le_jacobson _ _ (by simpa only [Ideal.jacobson_bot] using hI)
  refine Ideal.Quotient.eq_zero_iff_mem.1 (hH.haus _ fun n => ?_)
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by simpa using hi
  have h1 := Ideal.mem_map_of_mem Φ (TB.approx x n _ hF)
  have e : Φ.comp s = s.comp φ := RingHom.ext fun a => (hφ a).symm
  rw [Ideal.map_map, e, ← Ideal.map_map, Ideal.map_pow] at h1
  have h2 := TB.c_mem_of_mem_map _ _ (Ideal.map_mono (Ideal.pow_right_mono hφI n) h1) j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sub, map_sum, map_sum] at h2
  have h3 : ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i)) ∈ N :=
    N.sum_mem fun i _ => by
      rw [map_mul, ← hφ, TB.c_mul]
      exact N.mul_mem_right _ (hN i)
  have h4 : Ideal.Quotient.mk N (TB.c j (Φ x)) =
      (TB.c j (Φ x) - ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i))) • (1 : S ⧸ N) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simpa using h3
  rw [SModEq.zero, h4]
  exact Submodule.smul_mem_smul h2 Submodule.mem_top

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

theorem prime_l : Prime (l : (Wq l a)⟦X⟧) := by
  have key : ∀ x : (Wq l a)⟦X⟧, (l : (Wq l a)⟦X⟧) ∣ x →
      PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) x = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [map_mul, map_natCast, l_eq_zero, zero_mul]
  refine ⟨l_ne_zero l a, fun h => ?_, fun x y h => ?_⟩
  · have := key 1 h.dvd
    rw [map_one] at this
    exact one_ne_zero this
  · have := key _ h
    rw [map_mul] at this
    exact (mul_eq_zero.1 this).imp (dvd_of_map_eq_zero l a x) (dvd_of_map_eq_zero l a y)

theorem ne_zero_of_isPer {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := h
  rw [map_zero, eq_comm, Units.mul_right_eq_zero, sub_eq_zero] at h
  have h1 : ε = 1 := by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa using this
  exact hδ1 (by rw [h1, map_one, map_one])

end GlobalTheory.BSP.CoeffIdeal


open GlobalTheory.BSP.CoeffIdeal in
theorem GlobalTheory.BSP.pow_l_mem_span_coeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  intro l _ K bk τ hτ ι TB M
  set I : Ideal bk.S := Ideal.span (Set.range fun i => TB.c i (τ ^ M)) with hI
  have hJ : bk.J ≤ Ideal.jacobson ⊥ := by
    have := bk.complete
    exact IsAdicComplete.le_jacobson_bot _
  have hpr := prime_l l bk.a
  let P : Ideal bk.S :=
    { carrier := {x | ∃ r : ℕ, (l : bk.S) ^ r * x ∈ I}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨t, ht⟩
        refine ⟨r + t, ?_⟩
        have := I.add_mem (I.mul_mem_left ((l : bk.S) ^ t) hr) (I.mul_mem_left ((l : bk.S) ^ r) ht)
        convert this using 1
        ring
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact I.mul_mem_left c hr }
  have hsat : ∀ x, (l : bk.S) * x ∈ P → x ∈ P := by
    rintro x ⟨r, hr⟩
    exact ⟨r + 1, by rwa [pow_succ, mul_assoc]⟩
  have hIP : I ≤ P := fun x hx => ⟨0, by simpa using hx⟩
  obtain ⟨g, hg⟩ := principal_of_saturated
    (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)))
    (PowerSeries.map_surjective _ (WittVector.constantCoeff_surjective l)) (l : bk.S)
    (dvd_of_map_eq_zero l bk.a) (le_sup_left.trans hJ) P hsat
  have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
  have hdvd : ∀ i, g ∣ TB.c i (τ ^ M) := fun i => by
    rw [← Ideal.mem_span_singleton, ← hg]
    exact hIP (Ideal.subset_span ⟨i, rfl⟩)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact pow_ne_zero M (ne_zero_of_isPer l bk hτ) (TB.eq_zero_of_c _ fun i => zero_dvd_iff.1 (hdvd i))
  have hlg : ¬ (l : bk.S) ∣ g := by
    rintro ⟨y, hy⟩
    have h1 : y ∈ P := hsat y (hy ▸ hgP)
    rw [hg, Ideal.mem_span_singleton] at h1
    obtain ⟨z, hz⟩ := h1
    refine hpr.not_unit (IsUnit.of_mul_eq_one z (mul_left_cancel₀ hg0 ?_))
    rw [mul_one]
    conv_rhs => rw [hy, hz]
    ring
  have hφJ : bk.J.map (frobS l bk.a) ≤ bk.J := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    obtain ⟨b, hb⟩ := frobS_eq l bk.a bk.E
    rw [hb, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Fact.out : l.Prime).pos)
  have hE : ∀ j, frobS l bk.a g ∣ bk.E ^ M * TB.c j (τ ^ M) := fun j => by
    have := c_frob_mem TB hJ (frobS l bk.a) WittVector.frobenius bk.ev_frob hφJ (τ ^ M)
      (Ideal.span {frobS l bk.a g}) (fun i => Ideal.mem_span_singleton.2 (map_dvd _ (hdvd i))) j
    rwa [map_pow, hτ.1, mul_pow, ← map_pow, TB.c_mul, Ideal.mem_span_singleton] at this
  have hEI : ∀ x ∈ I, frobS l bk.a g ∣ bk.E ^ M * x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hE i
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left c
  obtain ⟨r, hr⟩ := hgP
  have hlφ : ¬ (l : bk.S) ∣ frobS l bk.a g := by
    obtain ⟨b, hb⟩ := frobS_eq l bk.a g
    rw [hb]
    intro h
    exact hlg (hpr.dvd_of_dvd_pow ((dvd_add_left (dvd_mul_right _ b)).1 h))
  have hfin : frobS l bk.a g ∣ bk.E ^ M * g := by
    obtain ⟨z, hz⟩ := hEI _ hr
    obtain ⟨w, hw⟩ : (l : bk.S) ^ r ∣ z :=
      hpr.pow_dvd_of_dvd_mul_left r hlφ ⟨bk.E ^ M * g, by rw [← hz]; ring⟩
    refine ⟨w, mul_left_cancel₀ (pow_ne_zero r hpr.ne_zero) ?_⟩
    rw [mul_left_comm, hz, hw]
    ring
  have hu := _root_.GlobalTheory.LemZ.isUnit_of_frob_dvd l K bk g hlg M hfin
  exact ⟨r, (I.mul_unit_mem_iff_mem hu).1 hr⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_gal_ev_E_unit {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (g : GQ l) :
    ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem WSeed.exists_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  intro l _ K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGA : ∀ y, G (bk.iA y) = bk.iA (Per.σA (g : GQ l) y) := hG.ext
  have hevE : bk.ev bk.E ≠ 0 := fun h => bk.frobenius_ev_E_ne_zero hτ (by rw [h, map_zero])
  have hE : bk.iS bk.E ≠ 0 := fun h => hevE (hinj (h.trans (map_zero _).symm))
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  obtain ⟨w, hw⟩ := exists_gal_ev_E_unit bk (g : GQ l)
  have hvu : bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hv0 : bk.iA (w : Ainf l) ≠ 0 := left_ne_zero_of_mul_eq_one hvu
  have hGE : G (bk.iS bk.E) = bk.iS bk.E * bk.iA (w : Ainf l) := by
    change G (bk.iA (bk.ev bk.E)) = _
    rw [hGA, hw, map_mul]
    rfl
  obtain ⟨li, hli⟩ : ∃ li : bk.DA bk.ρ₀, li * (l : bk.DA bk.ρ₀) = 1 := by
    obtain ⟨x, hx⟩ := (isUnit_l_disc l (bk.ev (PowerSeries.X : bk.S)) bk.ρ₀).exists_left_inv
    exact ⟨x, hx⟩
  have hnp : ∀ a b, ∃ c, (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) a b = bk.iS bk.E ^ (2 * s.N) * c :=
    fun a b => s.nopole g G hG a b
  choose Q hQ using hnp
  have hQm : s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G = bk.iS bk.E ^ (2 * s.N) • Matrix.of Q := by
    ext a b; rw [hQ a b]; rfl
  have hXX : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N) ≠ 0 := mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ hE)
  have hX'X := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hXX

  have hC1 : s.X.map bk.iS * Matrix.of Q = (l : bk.DA bk.ρ₀) ^ s.c₂ • (s.κ g * (s.X.map bk.iS).map G) := by
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero (2 * s.N) hE) ?_
    dsimp only
    rw [← Matrix.mul_smul, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_comm ((l : bk.DA bk.ρ₀) ^ s.c₂)]
  have hZi : IsUnit (Z.map i) := hZ.map (RingHom.mapMatrix i)
  have hZZ : Z.map i * (Z.map i)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hZi)
  refine ⟨(li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G), ?_, ?_⟩
  · have h3 : s.X.map bk.iS * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.X.map bk.iS * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (s.X.map bk.iS) (Z.map i), hZZ,
        Matrix.mul_one]
    have hs : G (bk.iS bk.E) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ =
        bk.iS bk.E ^ s.N := by
      rw [hGE]
      calc (bk.iS bk.E * bk.iA (w : Ainf l)) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) *
            (l : bk.DA bk.ρ₀) ^ s.c₂
          = bk.iS bk.E ^ s.N * (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N *
            (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli, one_pow, one_pow, mul_one, mul_one]
    rw [h3, hC1, Matrix.smul_mul, smul_smul, smul_smul, hs, Matrix.map_mul, ← Matrix.mul_assoc]
  · have hGXX : (s.X'.map bk.iS).map G * (s.X.map bk.iS).map G =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
      rw [← Matrix.map_mul, hX'X, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = s.W.map G * (Z.map i).map G := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_map, Matrix.map_map]
      congr 1
      funext y
      exact (hGA y).symm
    have hρ : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) =
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA := by
      rw [Matrix.map_map]; rfl
    have hL : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (s.W * s.X'.map bk.iS).map G *
        ((s.X.map bk.iS).map G * (Z.map i).map G) =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) •
          ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G * (Z.map i).map G) := by
      rw [Matrix.map_mul]
      calc _ = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G *
            ((s.X'.map bk.iS).map G * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hGXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have hR : s.W * s.X'.map bk.iS * s.κ g * ((s.X.map bk.iS).map G * (Z.map i).map G) =
        bk.iS bk.E ^ (2 * s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      calc _ = s.W * (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQm, Matrix.mul_smul, Matrix.smul_mul]
    have h5 := congrArg (· * ((s.X.map bk.iS).map G * (Z.map i).map G)) (s.gal g G hG)
    rw [Matrix.smul_mul, Matrix.smul_mul, hL, hR, smul_smul, smul_smul] at h5
    have h6 : s.W * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s.W (Z.map i), hZZ, Matrix.mul_one]
    rw [hYG, ← hρ, ← hWZ, h6, smul_smul, ← Matrix.mul_assoc]
    have hk : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hv0)) (pow_ne_zero _ hL0)
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) hk ?_
    dsimp only
    have hσE : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) =
        bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ) := by
      rw [map_mul, hw, map_mul, map_mul]; rfl
    have hE2 : bk.iA (bk.ev bk.E * τ) = bk.iS bk.E * bk.iA τ := by rw [map_mul]; rfl
    have hGc : G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) =
        (l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N) := by
      rw [map_mul, map_pow, map_pow, map_natCast, hGE]
    rw [hσE, hE2, hGc] at h5
    rw [smul_smul, smul_smul]
    have hs1 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ *
        (bk.iA (Per.σA (g : GQ l) τ) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N)) =
        (bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ)) ^ s.N * bk.iS bk.E ^ (2 * s.N) := by
      calc _ = bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ s.N * bk.iA (Per.σA (g : GQ l) τ) ^ s.N *
            (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N * (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli]; ring
    have hs2 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA τ ^ s.N =
        (bk.iS bk.E * bk.iA τ) ^ s.N * ((l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N)) := by
      ring
    rw [hs1, hs2]
    exact h5.symm

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittPowerSeriesApproxMatrixBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftMatK

variable {l : ℕ} [Fact l.Prime]

theorem pow_mul_mem_integers (K : FinExt l) (a : ↥K.1) : ∃ k : ℕ, (l : ↥K.1) ^ k * a ∈ OL K := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
    (PadicInt.irreducible_p (p := l))
  refine ⟨k, ?_⟩
  have h3 := hi.smul ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast] at h3
  exact h3

theorem lift_one (K : FinExt l) (bk : BK K) (C : Core l) (x : Om l) (hx : x ∈ K.1) (n : ℕ) :
    ∃ (m : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ m * C.o x ∈ Per.FilP l n := by
  obtain ⟨a, ha⟩ := pow_mul_mem_integers K ⟨x, hx⟩
  obtain ⟨k, s, hs, -⟩ := GlobalTheory.BSP.RingHomLiftCongruence.exists_lift l K bk C n ⟨_, ha⟩
  refine ⟨k + a, s, ?_⟩
  have e : ((((⟨_, ha⟩ : ↥(OL K)) : ↥K.1)) : Om l) = (l : Om l) ^ a * x := by
    simp
  rw [e, map_mul, map_pow, map_natCast, ← mul_assoc, ← pow_add] at hs
  exact hs

theorem lift_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  intro l _ K bk C d c hc n
  choose m s hs using fun i j => lift_one K bk C (c i j) (hc i j) n
  let M := Finset.univ.sup (fun p : Fin d × Fin d => m p.1 p.2)
  refine ⟨M, fun i j => (l : bk.S) ^ (M - m i j) * s i j, fun i j => ?_⟩
  have hle : m i j ≤ M := Finset.le_sup (f := fun p : Fin d × Fin d => m p.1 p.2) (Finset.mem_univ (i, j))
  have h := Ideal.mul_mem_left _ ((l : Per.BdRp l) ^ (M - m i j)) (hs i j)
  simp only [map_mul, map_pow, map_natCast]
  convert h using 1
  rw [mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.LiftMatK
end
end

