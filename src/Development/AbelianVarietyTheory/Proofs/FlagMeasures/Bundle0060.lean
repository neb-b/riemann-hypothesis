module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatIffMemLocP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruence
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocCongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem approx_int (A : Places F E sig) (g : ℕ) (hg : 0 < g) (p : HeightOneSpectrum (𝓞 F))
    (z : (A.loc p).Ep) (hz : z ∈ (A.L p).O) :
    ∃ x : 𝓞 E, ∃ o ∈ (A.L p).O, z - (A.loc p).ιE (x : E) = (A.loc p).ιE (g : E) * o := by
  have hgF : ((g : ℤ) : F) ≠ 0 := by exact_mod_cast hg.ne'
  let c : ∀ q, ((A.loc q).Fp)ˣ := fun q => Units.mk0 ((g : ℤ) : (A.loc q).Fp) (by
    rw [← map_intCast (A.loc q).ιF]; exact (map_ne_zero _).2 hgF)
  have hc := PlacesInt.intCast_isUnit_almost_all A (g : ℤ) (by exact_mod_cast hg.ne')
  have hcE : ∀ q, algebraMap (A.loc q).Fp (A.loc q).Ep (c q) = (A.loc q).ιE (g : E) := by
    intro q
    change algebraMap (A.loc q).Fp (A.loc q).Ep ((g : ℤ) : (A.loc q).Fp) = _
    rw [map_intCast, map_natCast, Int.cast_natCast]
  have hgO : ∀ q, (A.loc q).ιE (g : E) ∈ (A.L q).O := fun q => by
    rw [map_natCast]; exact natCast_mem (A.L q).O g
  let y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p z
  have hy : {q | y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  obtain ⟨-, hE, -⟩ := StrongApprox.strong_approx_additive A c hc
  obtain ⟨x, hx⟩ := hE y hy
  have hint : ∀ q, (A.loc q).ιE x ∈ (A.L q).O := by
    intro q
    obtain ⟨o, ho, he⟩ := hx q
    have hyq : y q ∈ (A.L q).O := by
      by_cases h : q = p
      · subst h
        change Pi.single (M := fun q => (A.loc q).Ep) q z q ∈ (A.L q).O
        rw [Pi.single_eq_same]; exact hz
      · change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
        rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : (A.loc q).ιE x = y q + algebraMap (A.loc q).Fp (A.loc q).Ep (c q) * o := by
      rw [← he]; ring
    rw [e, hcE]
    exact add_mem hyq (mul_mem (hgO q) ho)
  obtain ⟨xo, hxo⟩ := ((PlacesInt.integers_local A).1 x).1 hint
  obtain ⟨o, ho, he⟩ := hx p
  refine ⟨xo, -o, neg_mem ho, ?_⟩
  have hyp : y p = z := by
    change Pi.single (M := fun q => (A.loc q).Ep) p z p = z
    exact Pi.single_eq_same _ _
  rw [hyp, hcE] at he
  rw [hxo]
  linear_combination -he

section
variable (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}

theorem bc_sub (u v : Fin N → E) : A.bc p (u - v) = A.bc p u - A.bc p v := by
  funext i; simp [Places.bc]

theorem bc_smul (t : E) (u : Fin N → E) : A.bc p (t • u) = (A.loc p).ιE t • A.bc p u := by
  funext i; simp [Places.bc]

theorem bc_sum {ι : Type} (s : Finset ι) (f : ι → Fin N → E) :
    A.bc p (∑ i ∈ s, f i) = ∑ i ∈ s, A.bc p (f i) := by
  funext j; simp [Places.bc, Finset.sum_apply, map_sum]

theorem lat_smul (Λ : Submodule (𝓞 E) (Fin N → E)) (t : 𝓞 E) (v : Fin N → (A.loc p).Ep)
    (hv : v ∈ A.lat p Λ) : (A.loc p).ιE (t : E) • v ∈ A.lat p (Ideal.span {t} • Λ) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, hu, rfl⟩ := hw
    have e : (A.loc p).ιE (t : E) • A.bc p u = A.bc p (t • u) := by
      funext i
      change (A.loc p).ιE (t : E) * (A.loc p).ιE (u i) = (A.loc p).ιE (t • u i)
      rw [Algebra.smul_def, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hu, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o a _ ha =>
    have e : (A.loc p).ιE (t : E) • (o • a) = o • ((A.loc p).ιE (t : E) • a) := by
      change (A.loc p).ιE (t : E) • ((o : (A.loc p).Ep) • a) = (o : (A.loc p).Ep) • ((A.loc p).ιE (t : E) • a)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ o ha

end

theorem loc_cong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  intro F E _ _ _ _ _ sig A N r Λ hΛ g hg p y x ξp hO hlow hdiag hy hx
  choose ξ0 o ho hξ0 using fun a b => approx_int A g hg p (ξp a b) (hO a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else ξ0 a b
  have hd : ∀ a b, ∃ o ∈ (A.L p).O,
      ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E) = (A.loc p).ιE (g : E) * o := by
    intro a b
    by_cases h1 : b < a
    · refine ⟨0, zero_mem _, ?_⟩
      simp [ξ, h1, hlow a b h1]
    · by_cases h2 : a = b
      · subst h2
        refine ⟨0, zero_mem _, ?_⟩
        simp [ξ, hdiag]
      · refine ⟨o a b, ho a b, ?_⟩
        simp only [ξ, h1, h2, if_false]
        exact hξ0 a b
  have hFG : (Ideal.span {(g : 𝓞 E)} • Λ).FG := Submodule.FG.smul (Submodule.fg_span_singleton _) hΛ
  have hmem : ∀ b, A.bc p (x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a) ∈
      A.lat p (Ideal.span {(g : 𝓞 E)} • Λ) := by
    intro b
    rw [bc_sub, bc_sum]
    simp only [bc_smul]
    have e : A.bc p (x b) - ∑ a, (A.loc p).ιE ((ξ a b : 𝓞 E) : E) • A.bc p (y a) =
        (A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a)) +
          ∑ a, (ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E)) • A.bc p (y a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]; abel
    rw [e]
    refine add_mem (hx b) (Submodule.sum_mem _ fun a _ => ?_)
    obtain ⟨o', ho', he⟩ := hd a b
    rw [he, mul_smul]
    have h1 : (⟨o', ho'⟩ : (A.L p).O) • A.bc p (y a) ∈ A.lat p Λ := Submodule.smul_mem _ _ (hy a)
    have h2 := lat_smul A p Λ (g : 𝓞 E) _ h1
    have e2 : (((g : 𝓞 E) : E)) = (g : E) := by simp
    rw [e2] at h2
    exact h2
  refine ⟨ξ, fun a b h => by simp [ξ, h], fun a => by simp [ξ], fun P hP b => ?_⟩
  exact (LocDict.mem_lat_iff_mem_locP A N _ hFG p _).1 (hmem b) P hP

end GlobalTheory.HL.LocCongApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatBoundLocalLatticesStandardAeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_bound_localLattices_standard_ae : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → (∀ p, ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O) → ∃ N : ℕ, N ≠ 0 ∧ ∀ p, (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (N : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.exists_uniform_bound | exact GlobalTheory.HL.Glue.exists_uniform_bound | (intros; apply GlobalTheory.HL.Glue.exists_uniform_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatMulMemIntegersQuadraticCompletionStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_mem_integers_quadraticCompletion : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = o) → ∀ (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep), ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.exists_nat_mul_mem | exact GlobalTheory.HL.Glue.exists_nat_mul_mem | (intros; apply GlobalTheory.HL.Glue.exists_nat_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePairCoordinates_transport_unitary_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0) ∧ (∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0) ∧ Function.Bijective c.lat ∧ (∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ) ∧ (∀ g Λ, g ∈ LocNG.Aut Λ ↔ c.grp g ∈ MulAction.stabilizer S.GLV (c.lat Λ)) ∧ ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂) := by
  first | exact @GlobalTheory.HL.CoordMass.transport | exact GlobalTheory.HL.CoordMass.transport | (intros; apply GlobalTheory.HL.CoordMass.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMoveProperties
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveFacts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_form {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm y x = L.cj (hf L Hm x y) := by
  have h' : cT L Hm = Hm := h
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h' j) i
  unfold hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hf_add_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → E) : hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (x y : Fin n → E) : hf L Hm (c • x) y = c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hf_zero_left_flag_measures (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin n → E) : hf L Hm 0 y = 0 := by
  simp [hf]

theorem form_zero_of_span {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (A : Set (Fin n → E)) (hA : ∀ a ∈ A, ∀ b ∈ A, hf L Hm a b = 0) :
    ∀ x ∈ Submodule.span E A, ∀ y ∈ Submodule.span E A, hf L Hm x y = 0 := by
  intro x hx y hy
  have h1 : ∀ a ∈ A, ∀ z ∈ Submodule.span E A, hf L Hm z a = 0 := by
    intro a ha z hz
    induction hz using Submodule.span_induction with
    | mem w hw => exact hA w hw a ha
    | zero => exact hf_zero_left_flag_measures L Hm a
    | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
  induction hx using Submodule.span_induction with
  | mem w hw => rw [conj_form h y w, h1 w hw y hy, map_zero]
  | zero => exact hf_zero_left_flag_measures L Hm y
  | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
  | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem iso_spanTo (g : Fin (r + 1) → S.V) (c : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then c else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : S.h x x = 0 := by
  have hH : IsHerm L S.Hm := S.herm.1
  show hf L S.Hm x x = 0
  refine form_zero_of_span hH (g '' {i | (i : ℕ) < r}) ?_ x hx x hx
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : ℕ) < r := ha
  have hne : a ≠ Fin.last r := fun e => by subst e; simp at ha'
  rw [hg, if_neg (fun hc => hne hc.1)]

theorem mem_span_frame (g : Fin (r + 1) → S.V) (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r)
    (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    x ∈ Submodule.span E (Set.range fun b => n (g b)) := by
  have key : ∀ m : ℕ, m ≤ r → S.spanTo g m ≤ Submodule.span E (Set.range fun b => n (g b)) := by
    intro m
    induction m with
    | zero =>
      intro _
      unfold Frames.spanTo
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have h0 : n ∈ S.Nof g := hn
      unfold Frames.Nof at h0
      have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h0).1).2
      have hU : n ∈ unipOn (S.spanTo g (m + 1)) (S.spanTo g m) := Subgroup.mem_iInf.mp hI ⟨m, hm'⟩
      have hU' : (∀ v, n v ∈ S.spanTo g (m + 1) ↔ v ∈ S.spanTo g (m + 1)) ∧
          ∀ v ∈ S.spanTo g (m + 1), n v - v ∈ S.spanTo g m := hU
      have hsub : S.spanTo g (m + 1) ≤ Submodule.span E (Set.range fun b => n (g b)) := by
        unfold Frames.spanTo
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hgi : g i ∈ S.spanTo g (m + 1) := Submodule.subset_span ⟨i, hi, rfl⟩
        have h2 := ih hm'.le (hU'.2 (g i) hgi)
        have h3 : n (g i) ∈ Submodule.span E (Set.range fun b => n (g b)) :=
          Submodule.subset_span ⟨i, rfl⟩
        have h4 := Submodule.sub_mem _ h3 h2
        rwa [sub_sub_cancel] at h4
      exact hsub
  exact key (j + 1) (Nat.succ_le_of_lt j.2) hx

theorem parts_of_mem_Mof (hth : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O)
    (g g' : Fin (r + 1) → S.V) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ ξ ∈ Submodule.span L.O (Set.range g), ∃ ξ' ∈ Submodule.span L.O (Set.range g'),
      algebraMap F E S.th • m = ξ + ξ' := by
  have hinv : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨algebraMap F E S.th • g b, ?_, 0, zero_mem _, by rw [add_zero]⟩
      exact Submodule.smul_mem _ (⟨algebraMap F E S.th, hO⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · refine ⟨-g b, neg_mem (Submodule.subset_span ⟨b, rfl⟩), g' b, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
      show algebraMap F E S.th • algebraMap F E S.th⁻¹ • (g' b - g b) = -g b + g' b
      rw [smul_smul, hinv, one_smul, sub_eq_neg_add]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    obtain ⟨b, hb, b', hb', e'⟩ := hv
    exact ⟨a + b, add_mem ha hb, a' + b', add_mem ha' hb', by rw [smul_add, e, e']; abel⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    refine ⟨c • a, Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', ?_⟩
    show algebraMap F E S.th • ((c : E) • u) = (c : E) • a + (c : E) • a'
    rw [smul_smul, mul_comm (algebraMap F E S.th) (c : E), ← smul_smul, e, smul_add]

theorem move_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hin, -, -, huperp, ⟨c, hcO, hs⟩, -⟩ := hM
  obtain ⟨y, hyΛ, hxy⟩ := id hin
  obtain ⟨⟨-, -, hint⟩, -⟩ := hF
  have hj : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.2
  have hxX : x ∈ S.X := spanTo_mono S S.f hj hx
  have hx'X : x' ∈ S.X' := spanTo_mono S S.f' hj hx'
  have hH : IsHerm L S.Hm := S.herm.1
  have hxx : S.h x x = 0 := iso_spanTo S S.f _ S.gram x hxX
  have hx'x' : S.h x' x' = 0 := iso_spanTo S S.f' _ S.gram' x' hx'X
  have hperp : ∀ z ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm u z = 0 := huperp
  have hux : S.h u x = 0 := hperp x (Submodule.mem_sup_left hx)
  have hux' : S.h u x' = 0 := hperp x' (Submodule.mem_sup_right hx')
  obtain ⟨c0, hc0, he⟩ := hint x hxX x' hx'X x hxX x' hx'X hin hin
  have he' : hf L S.Hm x x' = algebraMap F E S.th * c0 := he
  have hcross : S.h x' x = algebraMap F E S.th * L.cj c0 := by
    show hf L S.Hm x' x = _
    rw [conj_form hH x x', he', map_mul, AlgEquiv.commutes]
  obtain ⟨-, hW, -, hfrL, hfr'L, hli, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -⟩ := hW
  obtain ⟨-, -, -, -, -, hth, hthO, -⟩ := GlobalTheory.FrameBasic.frames_basic L r k S
  obtain ⟨-, -, -, -, -, -, -, -, hMa, -, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hthE : algebraMap F E S.th ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr hthO
  have hinv : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  have hsum : x + x' ∈ S.ME :=
    add_mem (Submodule.mem_sup_left (spanTo_mono S S.f (by omega) hx))
      (Submodule.mem_sup_right (spanTo_mono S S.f' (by omega) hx'))
  have hyeq : y = algebraMap F E S.th⁻¹ • (x + x') := by
    rw [hxy, smul_smul, hinv, one_smul]
  have hyME : y ∈ S.ME := by rw [hyeq]; exact Submodule.smul_mem _ _ hsum
  have hysat : y ∈ S.sat Λ := Submodule.mem_inf.mpr ⟨hyΛ, hyME⟩
  obtain ⟨ξ, hξ, ξ', hξ', hsplit⟩ :=
    parts_of_mem_Mof S hth hthE (S.fr d Λ) (S.fr' d Λ) _ (hMa y hysat)
  set P := algebraMap F E ((S.ϖ : F) ^ S.a) with hP
  have hsplit' : P • x + P • x' = ξ + ξ' := by
    rw [← smul_add, hxy, smul_comm]; exact hsplit
  have hxfr : x ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    mem_span_frame S S.f (S.wit d Λ).1 hn j x hx
  have hx'fr : x' ∈ Submodule.span E (Set.range (S.fr' d Λ)) :=
    mem_span_frame S S.f' (S.wit d Λ).2 hn' j x' hx'
  have hdis := (linearIndependent_sum.mp hli).2.2
  have hw1 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hxfr)
      (Submodule.span_le_restrictScalars L.O E _ hξ)
  have hw2 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr' d Λ)) := by
    have e : P • x - ξ = ξ' - P • x' := by
      rw [sub_eq_sub_iff_add_eq_add, hsplit', add_comm]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.span_le_restrictScalars L.O E _ hξ')
      (Submodule.smul_mem _ _ hx'fr)
  have hPx : P • x = ξ := sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hw1 hw2)
  have hPx' : P • x' = ξ' := by rw [hPx] at hsplit'; exact add_left_cancel hsplit'
  have hfrΛ : ∀ b, S.fr d Λ b ∈ Λ := fun b =>
    ((hfrL (r + 1) le_rfl (S.fr d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hfr'Λ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr'L (r + 1) le_rfl (S.fr' d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hξΛ : ξ ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfrΛ b) hξ
  have hξ'Λ : ξ' ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfr'Λ b) hξ'
  have key : ∀ z, P • z ∈ Λ → s • z ∈ Λ ∧ L.cj s • z ∈ Λ := by
    intro z hz
    have hc' : L.cj c ∈ L.O := GlobalTheory.UnramOrder.cj_mem L hcO
    have h1 : s • z = (⟨c, hcO⟩ : L.O) • (P • z) := by
      rw [hs]; show (P * c) • z = c • (P • z); rw [smul_smul, mul_comm c P]
    have h2 : L.cj s • z = (⟨L.cj c, hc'⟩ : L.O) • (P • z) := by
      rw [hs, map_mul, AlgEquiv.commutes]; show (P * L.cj c) • z = L.cj c • (P • z)
      rw [smul_smul, mul_comm (L.cj c) P]
    exact ⟨h1 ▸ Λ.smul_mem _ hz, h2 ▸ Λ.smul_mem _ hz⟩
  have kx := key x (hPx ▸ hξΛ)
  have kx' := key x' (hPx' ▸ hξ'Λ)
  exact ⟨kx.1, kx.2, kx'.1, kx'.2, ⟨L.cj c0, GlobalTheory.UnramOrder.cj_mem L hc0, hcross⟩, hxx, hx'x',
    hux, hux', hxX, hx'X⟩

end GlobalTheory.HL.MoveFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordInnerFst

open CoordInnerSnd


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.CoordInnerFst.transport : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k)
    (c : _root_.GlobalTheory.HL.Coord P S),
    Function.Injective (c.inn P.A.f) ∧
    (∀ L, P.A.IsInner L ↔ S.IsInner S.f S.es
      (c.inn P.A.f L)) ∧
    (∀ A, S.IsInner S.f S.es A →
      ∃ L, A = c.inn P.A.f L) ∧
    ∀ L, c.lat (P.A.LamStd L) =
      S.stdLat S.f S.es
        (c.inn P.A.f L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hPID : IsPrincipalIdealRing M.L.O :=
    (_root_.GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => _root_.GlobalTheory.UnramOrder.cj_mem M.L hx
  have hT : P.A.T ≠ 0 := by
    rw [← c.T_eq]
    exact Units.ne_zero _
  exact ⟨_root_.GlobalTheory.HL.CoordInnerSnd.inn_inj P.A c,
    fun L => _root_.GlobalTheory.HL.CoordInnerSnd.isInner_iff P.A c S.f S.es hcj hPID hT
      c.f_eq c.es_eq L,
    _root_.GlobalTheory.HL.CoordInnerSnd.inn_surj P.A c S.f S.es
      c.f_eq,
    _root_.GlobalTheory.HL.CoordInnerSnd.lat_lamStd P.A c S.f S.es
      c.f_eq c.es_eq⟩

end GlobalTheory.HL.CoordInnerFst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiplesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples : ∀ {E : Type} [Field E] [NumberField E], ∀ (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → (∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ) → (∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) → Submodule.IsLattice E Γ := by
  first | exact @GlobalTheory.glue_latt_isLattice | exact GlobalTheory.glue_latt_isLattice | (intros; apply GlobalTheory.glue_latt_isLattice <;> assumption)
end

