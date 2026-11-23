module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemMIff
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0077

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.EvenBlockRowActionEval
section
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G

noncomputable section

namespace Formalism.L2.G.Cmp

section GlobalTheory

variable {K : Type} [Field K] {k n : ℕ}

theorem eval_rowAct (g : Matrix (Fin k) (Fin k) K) (f : MvPolynomial (Fin k × Fin n) K) (z : Matrix (Fin k) (Fin n) K) :
    eval (fun x => z x.1 x.2) (rowAct K g f) = eval (fun x => (g * z) x.1 x.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.mul_apply]

theorem even_block_row_action_eval (g : Matrix (Fin k) (Fin k) K) (e : ℤ) (f : MvPolynomial (Fin k × Fin k) K)
    (z : Matrix (Fin k) (Fin k) K) :
    z.det ^ e * eval (fun x => z x.1 x.2) (g.det ^ (-e) • rowAct K g⁻¹ f) =
      (g⁻¹ * z).det ^ e * eval (fun x => (g⁻¹ * z) x.1 x.2) f := by
  rw [MvPolynomial.smul_eval, eval_rowAct, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    mul_zpow, _root_.inv_zpow']
  ring

theorem even_block_weyl_mem {O : Type} [CommRing O] [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    ∃ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
        (g⁻¹ * z).det ^ lam (Fin.last m) * eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) := by
  rw [dw_eq hinj m lam hlam g hg] at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.1 hF
  obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hF0)
  refine ⟨f, hf, fun z => ?_⟩
  have e1 : map (algebraMap O K) f = rowAct K g F0 := hfeq
  have key : eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) = eval (fun x => z x.1 x.2) F0 := by
    rw [e1, eval_rowAct, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, MvPolynomial.smul_eval]
  rw [key, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_zpow, _root_.inv_zpow']
  ring

def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev

def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev

def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')

end GlobalTheory

section Prod

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_prod (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (y : Formalism.L2.Forms.Frames G) :
    evC P h pos G M (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (F v s))) y =
      ∏ v, ∏ s : Fin (P.n' v), ((zAt P h pos M y.1 v s).det ^ (eAt P v s) *
        eval (fun x => zAt P h pos M y.1 v s x.1 x.2) (F v s)) := by
  simp only [evC, LinearMap.coe_mk, AddHom.coe_mk, map_prod, blockEmb, MvPolynomial.eval_rename]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

end Prod

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain WithZero

section CRT

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem exists_prime_to_le (P : HeightOneSpectrum R) (d : R) (hd : d ≠ 0) :
    ∃ s : R, s ∉ P.asIdeal ∧ ∀ v : HeightOneSpectrum R, v ≠ P → v.intValuation s ≤ v.intValuation d := by
  classical
  have hI : (Ideal.span {d} : Ideal R) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  let S : Finset (HeightOneSpectrum R) := (Ideal.finite_factors hI).toFinset ∪ {P}
  let n : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v = P then 1 else n v) (fun v _ => v.prime)
    (fun v _ v' _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then 1 else 0)
  refine ⟨y, ?_, fun v hv => ?_⟩
  · intro hyP
    have h1 := hy P (Finset.mem_union_right _ (Finset.mem_singleton_self P))
    simp only [↓reduceIte, pow_one] at h1
    have h2 : (1 : R) ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hyP h1
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · by_cases hvd : v.asIdeal ∣ Ideal.span {d}
    · have hvS : v ∈ S := Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hvd)
      have h1 := hy v hvS
      simp only [if_neg hv, sub_zero] at h1
      rw [v.intValuation_if_neg hd]
      exact (v.intValuation_le_pow_iff_mem y (n v)).2 h1
    · have h3 : v.intValuation d = 1 := by
        apply le_antisymm (v.intValuation_le_one d)
        by_contra hlt
        exact hvd ((v.intValuation_lt_one_iff_dvd d).1 (lt_of_not_ge hlt))
      rw [h3]
      exact v.intValuation_le_one y

end CRT

variable {D : D7}

theorem exists_den (u : D.what₂.Word) (x : ((D.fm u).lat 0).V) :
    ∃ d : 𝓞 D.what₂.LL, d ≠ 0 ∧ d • x ∈ ((D.fm u).lat 0).L :=
  _root_.UpperTheory.Reformulated.B.ExistsDenominatorThird.exists_den u x

theorem locWBack_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWBack T := by
  intro u w x hx
  have key : ∀ (r : 𝓞 D.what₂.LL) (v : ((D.fm u).lat 0).V), r • v = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) • v :=
    fun r v => (algebraMap_smul D.what₂.LL r v).symm
  obtain ⟨d, hd0, hdL⟩ := exists_den u x
  obtain ⟨s, hsP, hsv⟩ := exists_prime_to_le (D.plEq w) d hd0
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ Submodule.zero_mem _)
  have hsL : s • x ∈ ((D.fm u).lat 0).L := by
    refine (((T u).val0).lat (s • x)).2 ?_
    intro w' c B hB
    by_cases hw : w' = w
    · subst hw
      have hsint : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (D.plEq w').intValuation_le_one s
      obtain ⟨P, hP, hPx⟩ := hx c B hB
      refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) • P, intSpan_smul w' _ _ hsint hP, fun t => ?_⟩
      rw [key, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
    · have hne : D.plEq w' ≠ D.plEq w := fun h => hw (D.plEq.injective h)
      have hdne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        simpa using hd0
      set q : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL s / algebraMap (𝓞 D.what₂.LL) D.what₂.LL d with hq
      have hqint : q ∈ intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [val_nonneg_iff, hq, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        have hdv : (D.plEq w').intValuation d ≠ 0 := (D.plEq w').intValuation_ne_zero d hd0
        rw [div_le_one₀ (zero_lt_iff.2 hdv)]
        exact hsv _ hne
      have hsx : s • x = q • (d • x) := by
        rw [key, key, smul_smul, hq, div_mul_cancel₀ _ hdne]
      obtain ⟨P, hP, hPx⟩ := (((T u).val0).lat (d • x)).1 hdL w' c B hB
      refine ⟨D.what₂.embLL q • P, intSpan_smul w' _ q hqint hP, fun t => ?_⟩
      rw [hsx, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]

  have hsu : (D.plEq w).intValuation s = 1 := by
    apply le_antisymm ((D.plEq w).intValuation_le_one s)
    by_contra hlt
    exact hsP (((D.plEq w).intValuation_lt_one_iff_mem s).1 (lt_of_not_ge hlt))
  have hsne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by simpa using hs0
  have htint : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
    rw [val_nonneg_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hsu, inv_one]
  have hx' : x = (⟨_, htint⟩ : intW D.what₂.places w) • (s • x) := by
    rw [Subring.smul_def, key, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsL)

theorem locWCrit_proved (T : ∀ u : D.what₂.Word, Forms0 D u) : LocWCrit T :=
  locWCrit_of T (locWBack_proved T)

end Formalism.L2.G.Cmp
end
end

