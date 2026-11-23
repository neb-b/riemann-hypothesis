module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.ExpCond

theorem not_mem_sq_of_not_dvd_discr {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hvZ : ((p : ℤ) : 𝓞 E) ∈ w.asIdeal := by simpa using hv
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd w.asIdeal w.isPrime hvZ
  have hunder : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    symm
    refine (PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible).eq_of_le
      (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hv)
  let := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under ℤ) w.asIdeal
  have hloc := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (w.asIdeal.under ℤ) w.asIdeal).mp hun).2
  have h1 := (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot Ideal.map_comap_le).mpr hloc
  refine (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mpr ?_ h1
  have hunder' : Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal = Ideal.span {(p : ℤ)} := hunder
  rw [hunder', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using h2

variable {E : Type} [Field E] [NumberField E]

theorem mem_below (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) : (p : OF E) ∈ (below w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  show (p : OF E) ∈ Ideal.comap (algebraMap (OF E) (𝓞 E)) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

theorem emult_zero (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (h : (p : 𝓞 E) ∉ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_span_singleton, mem_below]
  exact h

theorem emult_one (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (h : (p : 𝓞 E) ∈ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 1 := by
  have hle : Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal ≤ w.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => hx)
  have hdvd : (below w).asIdeal ^ 1 ∣ Ideal.span {(p : OF E)} := by
    rw [pow_one, Ideal.dvd_span_singleton, mem_below]
    exact h
  have hndvd : ¬ (below w).asIdeal ^ (1 + 1) ∣ Ideal.span {(p : OF E)} := by
    intro h2
    rw [Ideal.dvd_span_singleton] at h2
    have hm := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at hm
    have hsq : (Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal) ^ (1 + 1) ≤ w.asIdeal ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, pow_two]
      exact Ideal.mul_mono hle hle
    exact not_mem_sq_of_not_dvd_discr hp hd w h (hsq hm)
  have := (emultiplicity_eq_coe (n := 1)).mpr ⟨hdvd, hndvd⟩
  simpa using this

theorem not_mem_of_ne (w : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : (p : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro hq'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hc
  have e : (u : 𝓞 E) * (p : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hq')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem emult_cond (v v0 : HeightOneSpectrum (OF E)) (a b c d : ℕ) :
    emultiplicity v.asIdeal (Ideal.span {((a * b * c * d : ℕ) : OF E)} ^ 2 * v0.asIdeal) =
      2 * (emultiplicity v.asIdeal (Ideal.span {(a : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(b : OF E)}) +
        emultiplicity v.asIdeal (Ideal.span {(c : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(d : OF E)})) +
        emultiplicity v.asIdeal v0.asIdeal := by
  have hv := v.prime
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    emultiplicity_mul hv, emultiplicity_pow hv, emultiplicity_mul hv, emultiplicity_mul hv,
    emultiplicity_mul hv]
  push_cast
  ring

theorem emult_ne {v v0 : HeightOneSpectrum (OF E)} (h : v ≠ v0) : emultiplicity v.asIdeal v0.asIdeal = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
  intro hle
  apply h
  exact HeightOneSpectrum.ext ((v0.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem emult_self (v : HeightOneSpectrum (OF E)) : emultiplicity v.asIdeal v.asIdeal = 1 := by
  simpa using emultiplicity_pow_self_of_prime v.prime 1

end GlobalTheory.LamTie.ExpCond

namespace GlobalTheory.LamTie

open ExpCond

theorem expIn_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧
      (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧
      (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  intro R H q0 w0 hP w
  obtain ⟨hw0, hdist, hspl⟩ := hP
  have hq0 : (q0 : 𝓞 H.E) ∈ w0.asIdeal := hw0
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, or_false] at hdist
  have pr : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hspl p hp).1
  have dc : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ¬ (p : ℤ) ∣ discr H.E := fun p hp => (hspl p hp).2.2.1
  have uniq : ∀ x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0],
      (x : 𝓞 H.E) ∈ w.asIdeal → (y : 𝓞 H.E) ∈ w.asIdeal → x = y := by
    intro x hx y hy mx my
    by_contra hxy
    exact not_mem_of_ne w (pr x hx) (pr y hy) hxy mx my
  have key : emultiplicity (below w).asIdeal (cond0 H w0) =
      2 * (emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)})) +
      emultiplicity (below w).asIdeal (below w0).asIdeal :=
    emult_cond (below w) (below w0) (H.g 0) (H.g 1) H.pde H.pde'
  have qw : below w = below w0 → (q0 : 𝓞 H.E) ∈ w.asIdeal := fun heq =>
    (mem_below w q0).mp (heq ▸ (mem_below w0 q0).mpr hq0)
  have toExp : ∀ n : ℕ, emultiplicity (below w).asIdeal (cond0 H w0) = n → expIn (cond0 H w0) (below w) = n :=
    fun n h => multiplicity_eq_of_emultiplicity_eq_some h
  have m0 : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m1 : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m2 : (H.pde : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m3 : (H.pde' : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have n0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 0 :=
    emult_zero w
  have n1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 0 :=
    emult_zero w
  have n2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 0 :=
    emult_zero w
  have n3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 0 :=
    emult_zero w
  have u := fun x (hx : x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0]) y (hy : y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0])
    (hne : x ≠ y) (mx : (x : 𝓞 H.E) ∈ w.asIdeal) (my : (y : 𝓞 H.E) ∈ w.asIdeal) => hne (uniq x hx y hy mx my)
  refine ⟨fun hO => ?_, fun heq => ?_, fun hO hne => ?_⟩
  · have hne : below w ≠ below w0 := by
      intro heq
      have hq := qw heq
      rcases hO with ⟨k, hk⟩ | hk | hk
      · fin_cases k
        · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
        · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
    apply toExp
    rw [key, emult_ne hne]
    rcases hO with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m0 hk, n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
      · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m1 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
    · have hk : (H.pde : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m2 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
    · have hk : (H.pde' : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m3 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
  · have hq := qw heq
    have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    refine ⟨?_, ?_⟩
    · rintro (⟨k, hk⟩ | hk | hk)
      · fin_cases k
        · exact a0 hk
        · exact a1 hk
      · exact a2 hk
      · exact a3 hk
    · apply toExp
      rw [key, n0 a0, n1 a1, n2 a2, n3 a3, heq, emult_self]
      norm_num
  · have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨0, h⟩)
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨1, h⟩)
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inl h))
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inr h))
    apply toExp
    rw [key, n0 a0, n1 a1, n2 a2, n3 a3, emult_ne hne]
    norm_num

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.HTBasis

variable {l : ℕ} [Fact l.Prime]

def repOf {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp r)

theorem repOf_apply {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (v : Fin m → ↥LL.1) :
    repOf r g v = (r g : Matrix (Fin m) (Fin m) ↥LL.1).mulVec v := rfl

variable (P : LocPrime l) (LL : FinExt l) (m : ℕ)

def embF : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp LL.1.val

theorem embF_apply (x : ↥LL.1) : embF P LL x = algebraMap (Om l) P.R.BdR (x : Om l) := rfl

def mulF : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (embF P LL) (AlgHom.id ℚ_[l] P.R.BdR) fun _ _ => Commute.all _ _

@[simp] theorem mulF_tmul (c : ↥LL.1) (b : P.R.BdR) : mulF P LL (c ⊗ₜ[ℚ_[l]] b) = embF P LL c * b := by
  simp [mulF]

def coordF : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin m → P.R.BdR) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : Fin m → ↥LL.1) (b : P.R.BdR) j => embF P LL (v j) * b)
    (fun v v' b => by funext j; simp [add_mul])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_assoc])
    (fun v b b' => by funext j; simp [mul_add])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_left_comm]))

@[simp] theorem coordF_tmul (v : Fin m → ↥LL.1) (b : P.R.BdR) :
    coordF P LL m (v ⊗ₜ[ℚ_[l]] b) = fun j => embF P LL (v j) * b := rfl

section Lemmas

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (m : ℕ)

theorem coordF_sm (r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) r x) = mulF P LL r • coordF P LL m x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add (f := _), LinearMap.add_apply, hr, hs, add_smul]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
    | tmul v b' =>
      funext j
      simp only [GlobalTheory.DRFil.sm_tmul, coordF_tmul, mulF_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring

theorem embF_mem_fil (K : FinExt l) (c : ↥LL.1) : embF P LL c ∈ (P.PD K).Fil 0 :=
  (GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem _)

theorem coordF_mem_fil (K : FinExt l) {n : ℤ} {x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n) (j : Fin m) :
    coordF P LL m x j ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K (v j)) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_mem_fil (K : FinExt l) {n : ℤ} {r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR}
    (hr : r ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) n) : mulF P LL r ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _)]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K v) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_idem (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥K.1, ((τ x : ↥LL.1) : Om l) = (x : Om l)) :
    mulF P LL (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  have e : ∀ i, mulF P LL (a i ⊗ₜ[ℚ_[l]] algebraMap ↥K.1 P.R.BdR (c i)) =
      algebraMap (Om l) P.R.BdR (((a i * τ (c i) : ↥LL.1)) : Om l) := by
    intro i
    rw [mulF_tmul, embF_apply, IntermediateField.coe_mul, map_mul, hτ]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_sum]
  have h2 := congrArg (fun x : ↥LL.1 => (x : Om l)) h1
  simp only [IntermediateField.coe_sum, IntermediateField.coe_one] at h2
  simp only [IntermediateField.coe_mul] at h2 ⊢
  rw [h2, map_one]

theorem coordF_act (K : FinExt l) (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (hg : ∀ x ∈ LL.1, (g : GQ l) x = x) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (actVdR (P.PD K) (repOf r) g x) =
      ((r g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
        (fun j => P.actQdR (g : GQ l) (coordF P LL m x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    have hfix : ∀ c : ↥LL.1, P.actQdR (g : GQ l) (embF P LL c) = embF P LL c := fun c => by
      rw [embF_apply, P.actQdR_Om, hg _ c.2]
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actVdR, AlgebraTensorModule.map_tmul, coordF_tmul, repOf_apply, P.PD_actdR,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, hfix, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    rw [mul_assoc]
    exact congrArg _ (congrArg _ (P.PD_actdR K g b))

end Lemmas

section Theta

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def thetaOf (T : LocTied l P AI) : Formalism.MainNotions.LocalSituation.ThetaL P AI :=
  (GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI T).some

def colHT (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℂ_[l] :=
  Matrix.of fun j i => J.θ (((GlobalTheory.DeRhamSymbol.tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j)

end Theta

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CobCrisLift

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem tmul_mem (v : V) {a : ℤ} {b : BdR} (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] (⟨b, hb⟩ : (PD.Fil a).restrictScalars Qp), by simp⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [AlgebraTensorModule.map_tmul]
    exact tmul_mem PD _ (PD.Fil_anti a b.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem filV_exhaustive (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.inductionOn with
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem PD v ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem φVB_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sub_φ_mem_Dcris (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  refine (Submodule.mem_iInf _).2 fun g => ?_
  have h1 : φVB PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : B) := by
    simp [φVB]
  rw [hx g, map_sub, φVB_act] at h1
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_sub_sub_comm, h1,
    sub_self]

theorem act_ιV_sub_mem (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g : G) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) - ιV PD (LL := LL) (V := V) x ∈
      FilV PD (LL := LL) (V := V) 0 := by
  rw [← ιV_act, ← map_sub, ← hx g]
  have h1 : ιV PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : BdR) := by
    simp [ιV]
  rw [h1]
  exact tmul_mem PD _ PD.one_mem

end General

theorem coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  intro l _ P AI hT K LL _ _ _ O _ _ hO A hdR c x hx
  refine ⟨sub_φ_mem_Dcris (P.PD K) A.ρ c x hx, ?_⟩
  obtain ⟨a, ha⟩ := filV_exhaustive (P.PD K) (LL := LL) (ιV (P.PD K) (LL := LL) (V := A.V) x)
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.TateFilQuotTied.tied_tate_fil_quot l P AI hT K LL O hO A hdR a 0 _ ha
    (act_ιV_sub_mem (P.PD K) A.ρ c x hx)
  exact ⟨w, hw.1, hw'⟩

end GlobalTheory.CobCrisLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  first | exact @GlobalTheory.BSP.exists_discMap_of_pow_dvd | exact GlobalTheory.BSP.exists_discMap_of_pow_dvd | (intros; apply GlobalTheory.BSP.exists_discMap_of_pow_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_normal_subgroup_under_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)), IsOpen (H : Set (GE N)) → H.Normal → (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) → ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  first | exact @GlobalTheory.ResSel.SmallSub.exists_small | exact GlobalTheory.ResSel.SmallSub.exists_small | (intros; apply GlobalTheory.ResSel.SmallSub.exists_small <;> assumption)
end

