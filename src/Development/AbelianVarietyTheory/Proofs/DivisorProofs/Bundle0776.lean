module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajAtAddRight
section
open NumberField GlobalTheory.AllWt

namespace GlobalTheory.CutNum

open Module Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)

theorem fcoord_add' (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem fcoord_smul' (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem normAt_add_sq (x y : V) :
    normAt b X v (x + y) ^ 2 = normAt b X v x ^ 2 + normAt b X v y ^ 2 + 2 * (majAt b X v x y).re := by
  simp only [normAt, cnorm, majAt, fcoord_add']
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul_left' (a : K) (x y : V) :
    majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem majAt_add_right' (x y z : V) : majAt b X v x (y + z) = majAt b X v x y + majAt b X v x z := by
  simp only [majAt, fcoord_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem star_majAt' (x y : V) : star (majAt b X v x y) = majAt b X v y x := by
  simp only [majAt, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem selfAdj_of_pyth (hv : v.IsComplex) (e : V →ₗ[K] V)
    (h : ∀ x y, normAt b X v (e x + (y - e y)) ^ 2 = normAt b X v (e x) ^ 2 + normAt b X v (y - e y) ^ 2) (x y : V) :
    majAt b X v (e x) y = majAt b X v x (e y) := by
  have hre : ∀ x y, (majAt b X v (e x) (y - e y)).re = 0 := by
    intro x y
    have h1 := normAt_add_sq b X v (e x) (y - e y)
    have h2 := h x y
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply InfinitePlace.isComplex_iff.mp hv
    first
    | exact fun t => Complex.conj_eq_iff_im.mpr (hcon t)
    | (rw [ComplexEmbedding.isReal_iff]; ext t; exact Complex.conj_eq_iff_im.mpr (hcon t))
  have hzero : ∀ x y, majAt b X v (e x) (y - e y) = 0 := by
    intro x y
    have h0 := hre x y
    have h1 := hre (a • x) y
    rw [map_smul, majAt_smul_left'] at h1
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, h0] at h1
    have hm : (v.embedding a).im * (majAt b X v (e x) (y - e y)).im = 0 := by linarith
    refine Complex.ext (by simpa using h0) ?_
    rcases mul_eq_zero.mp hm with hm | hm
    · exact absurd hm ha
    · simpa using hm
  have hL : majAt b X v (e x) y = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e x) (e y) (y - e y)
    rw [hzero, add_zero, show e y + (y - e y) = y by abel] at this
    exact this
  have hR : majAt b X v x (e y) = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e y) (e x) (x - e x)
    rw [hzero, add_zero, show e x + (x - e x) = x by abel] at this
    rw [← star_majAt' b X v (e y) x, this, star_majAt']
  rw [hL, hR]

end Maj

theorem numeric {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 12) (hb : db ≤ 3 * δ * (dg + db))
    (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) : μ - 12 * δ * Q ≤ μg := by
  have hQ : 0 ≤ Q := by linarith
  have hδdb : δ * db ≤ 1 / 12 * db := mul_le_mul_of_nonneg_right hδ' hdb
  have hdg0 : 0 < dg := by
    rcases lt_or_eq_of_le hdg with h | h
    · exact h
    · subst h
      nlinarith
  have h4 : db ≤ 4 * δ * dg := by nlinarith
  have k1 : db * (-Q) ≤ db * μ := mul_le_mul_of_nonneg_left hμ hdb
  have k2 : db * Q ≤ 4 * δ * dg * Q := mul_le_mul_of_nonneg_right h4 hQ
  have k3 : db * m ≤ db * Q := mul_le_mul_of_nonneg_left hm hdb
  have k4 : db * lg ≤ db * Q := mul_le_mul_of_nonneg_left hlg hdb
  have key : dg * (μ - 12 * δ * Q) ≤ dg * μg := by nlinarith
  exact le_of_mul_le_mul_left key hdg0

theorem slope_good_ge : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ) (δ Q : ℝ), HasGram N → M.FG → L ≤ M → L ≠ ⊥ → e ∘ₗ e = e → (∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2) → 1 ≤ g → (∀ x ∈ L, (g : K) • e x ∈ L) → 0 ≤ δ → δ ≤ 1 / 12 → (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * Formalism.HN.rkK L → slopeMax_sq N M ≤ Q → -Q ≤ slope_sq N L → 2 * Real.log g ≤ Q → slope_sq N L - 12 * δ * Q ≤ slope_sq N (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint hδ hδ' hrk hmax hmin hlog
  letI : StarRing K := starRingOfComm
  obtain ⟨F⟩ := hGram
  obtain ⟨n, ⟨⟨b, X⟩, hG⟩⟩ := F
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  have hLfg : L.FG := Submodule.FG.of_le hM hLM
  have hRfg : (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)).FG :=
    Submodule.FG.of_le hM (inf_le_left.trans hLM)
  have hsa : ∀ v x y, majAt b X v (e x) y = majAt b X v x (e y) := by
    intro v
    apply selfAdj_of_pyth b X v (IsTotallyComplex.isComplex v) e
    intro x y
    simp only [(hG v).2]
    exact hpyth v.embedding x y
  obtain ⟨hrkadd, hcut, hmaj⟩ := Formalism.ExtensionFiltration.goodBadCut K V (Fin n) b X hX e g L hLfg hg hee hsa hint
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  rw [slope_sq_eq hG hLfg] at hmin ⊢
  rw [slope_sq_eq hG hRfg]
  rw [(slopeMax_slopeMin_eq hG hM hM0).1] at hmax
  have hne := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L hL0
  have hrkR : (Formalism.HN.rkK L : ℝ) = (Formalism.HN.rkK (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by
    exact_mod_cast hrkadd.symm
  have hpos : (0 : ℝ) < Formalism.HN.rkK L := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hmj := hmaj M hM hLM
  have hlg0 : 0 ≤ 2 * Real.log g := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have := Real.log_nonneg this
    linarith
  rw [hrkR] at hcut hrk hpos
  exact numeric hpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hδ hδ' hrk hmax hmin hlog hlg0

end GlobalTheory.CutNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

section Act

variable {G : Type} [Monoid G]

def act (T : G →₀ ℂ) (f : G → ℂ) (g : G) : ℂ :=
  T.sum fun k c => c * f (g * k)

def comp (T T' : G →₀ ℂ) : G →₀ ℂ :=
  T.sum fun a c => T'.sum fun b d => Finsupp.single (a * b) (c * d)

@[simp] theorem act_zero (f : G → ℂ) (g : G) : act (0 : G →₀ ℂ) f g = 0 := by
  simp [act]

theorem act_add (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (T + T') f g = act T f g + act T' f g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _

@[simp] theorem act_single (k : G) (c : ℂ) (f : G → ℂ) (g : G) :
    act (Finsupp.single k c) f g = c * f (g * k) :=
  Finsupp.sum_single_index (zero_mul _)

theorem act_finset_sum {ι : Type} (s : Finset ι) (T : ι → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (∑ i ∈ s, T i) f g = ∑ i ∈ s, act (T i) f g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, act_add, ih]

theorem act_finsupp_sum {α : Type} (T : α →₀ ℂ) (t : α → ℂ → G →₀ ℂ) (f : G → ℂ) (g : G) :
    act (T.sum t) f g = T.sum fun a c => act (t a c) f g :=
  act_finset_sum _ _ _ _

theorem act_comp (T T' : G →₀ ℂ) (f : G → ℂ) (g : G) : act (comp T T') f g = act T (act T' f) g := by
  unfold comp
  rw [act_finsupp_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only
  rw [act_finsupp_sum]
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [Finsupp.sum_single_index (zero_mul _), mul_assoc, mul_assoc]

theorem act_congr (T : G →₀ ℂ) {f f' : G → ℂ} {g : G} (h : ∀ k ∈ T.support, f (g * k) = f' (g * k)) :
    act T f g = act T f' g :=
  Finset.sum_congr rfl fun k hk => by simp only; rw [h k hk]

theorem mem_support_comp {T T' : G →₀ ℂ} {k : G} (hk : k ∈ (comp T T').support) :
    ∃ a ∈ T.support, ∃ b ∈ T'.support, k = a * b := by
  classical
  unfold comp Finsupp.sum at hk
  obtain ⟨a, ha, hk⟩ : ∃ a ∈ T.support,
      k ∈ (∑ b ∈ T'.support, Finsupp.single (a * b) (T a * T' b)).support := by
    exact Finset.mem_biUnion.1 (Finsupp.support_finsetSum hk)
  obtain ⟨b, hb, hk⟩ : ∃ b ∈ T'.support,
      k ∈ (Finsupp.single (a * b) (T a * T' b)).support := by
    exact Finset.mem_biUnion.1 (Finsupp.support_finsetSum hk)
  exact ⟨a, ha, b, hb, Finset.mem_singleton.1 (Finsupp.support_single_subset hk)⟩

theorem exists_fin (T : G →₀ ℂ) : ∃ (n : ℕ) (h : Fin n → G) (c : Fin n → ℂ),
    (∀ i, h i ∈ T.support) ∧ ∀ f g, act T f g = ∑ i, c i * f (g * h i) := by
  classical
  refine ⟨T.support.card, fun i => (T.support.equivFin.symm i).1, fun i => T (T.support.equivFin.symm i).1,
    fun i => (T.support.equivFin.symm i).2, fun f g => ?_⟩
  unfold act Finsupp.sum
  rw [← Finset.sum_coe_sort T.support]
  exact Fintype.sum_equiv T.support.equivFin _ _ fun x => by simp

end Act

variable {F : Type} [NormedField F]

def cell {n : ℕ} (z : GL (Fin n) F) (U : Set (GL (Fin n) F)) : Set (GL (Fin n) F) :=
  {g | ∃ u ∈ unipB F (Fin n), ∃ k ∈ U, g = u * z * k}

def Cuts (ψ : AddChar F ℂ) {n : ℕ} (U X A : Set (GL (Fin n) F)) : Prop :=
  ∃ T : GL (Fin n) F →₀ ℂ, ∀ f : GL (Fin n) F → ℂ, Eqv ψ f → (∀ u ∈ U, ∀ g, f (g * u) = f g) →
    ∀ g ∈ A, act T f g = X.indicator f g

end GlobalTheory.JSW.Cut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducible
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible

theorem exists_subset_natDegree_of_dvd_prod {k : Type} [Field k] {ι : Type} (P : ι → k[X])
    (hP : ∀ c, Irreducible (P c)) (s : Finset ι) :
    ∀ q : k[X], q ∣ ∏ c ∈ s, P c → ∃ A : Finset ι, A ⊆ s ∧ ∑ c ∈ A, (P c).natDegree = q.natDegree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    rw [Finset.prod_empty] at hq
    exact ⟨∅, Finset.Subset.refl _, by
      rw [Finset.sum_empty, natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hq)]⟩
  | insert i s hi ih =>
    intro q hq
    have hne : ∏ c ∈ insert i s, P c ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun c _ => (hP c).ne_zero
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero hne hq
    rw [Finset.prod_insert hi] at hq
    obtain ⟨q₁, q₂, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hq
    obtain ⟨A, hA, hsum⟩ := ih q₂ h2
    have hq1 : q₁ ≠ 0 := left_ne_zero_of_mul hq0
    have hq2 : q₂ ≠ 0 := right_ne_zero_of_mul hq0
    rw [natDegree_mul hq1 hq2]
    rcases (hP i).dvd_iff.mp h1 with hu | ha
    · exact ⟨A, hA.trans (Finset.subset_insert _ _), by
        rw [hsum, natDegree_eq_zero_of_isUnit hu, zero_add]⟩
    · refine ⟨insert i A, Finset.insert_subset_insert _ hA, ?_⟩
      rw [Finset.sum_insert (fun h => hi (hA h)), hsum,
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]

theorem natDegree_divisors_prod :
    ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  intro k _ ι _ P hP _
  refine ⟨fun a => ⟨?_, ?_⟩, fun Q => ⟨?_, ?_⟩⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨A, -, hA⟩ := exists_subset_natDegree_of_dvd_prod P (fun c => (hP c).2) _ q hq
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    exact ⟨∏ c ∈ A, P c, Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _),
      natDegree_prod_of_monic _ _ fun c _ => (hP c).1⟩
  · rintro ⟨q, hirr, hq, hQ⟩
    obtain ⟨c, -, hc⟩ := (Prime.dvd_finsetProd_iff hirr.prime _).mp hq
    have ha := hirr.associated_of_dvd (hP c).2 hc
    refine ⟨c, ?_⟩
    rwa [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ha)]
  · rintro ⟨c, hc⟩
    exact ⟨P c, (hP c).2, Finset.dvd_prod_of_mem _ (Finset.mem_univ c), hc⟩

end GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal

open Neutral.B1

theorem exists_uniformisation_torsTransport {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ≠ 0) :
    letI : Algebra K ℂ := ι.toAlgebra
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ :=
  GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod h2 ι Λ₀ Ω₀ hΛ hΩ

theorem exists_globalArtinMap {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (e : Ω ≃ₐ[K] AlgebraicClosure K) :
    ∃ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art ∧
      ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
        Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  obtain ⟨φ, hφc, hφb, hφ⟩ := _root_.GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e
  let ψ : Ideles K →* Field.absoluteGaloisGroupAbelianization K := φ.comp art⁻¹
  have hψ : ∀ s, ψ s = φ (art s)⁻¹ := fun s => rfl
  have hle : (diagUnits K).range ≤ ψ.ker := by
    rintro _ ⟨k, rfl⟩
    have hk : diagUnits K k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    rw [MonoidHom.mem_ker, hψ, MonoidHom.mem_ker.mp hk, inv_one, map_one]
  let Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K := QuotientGroup.lift _ ψ hle
  have hArt : ∀ s, Art (QuotientGroup.mk s) = φ ((art s)⁻¹) := fun s => rfl
  have hArtσ : ∀ (s : Ideles K) (σ : Formalism.ConjugateSelfDual.G K Ω), (art s)⁻¹ = GlobalTheory.HeckeGal.toAb K Ω σ →
      Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := fun s σ h => by
    rw [hArt, h, hφ]
  refine ⟨Art, ⟨?_, ?_, ?_, ?_, ?_⟩, hArtσ⟩
  · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    exact hφc.comp (ha.quot.continuous.inv)
  · intro c
    obtain ⟨y, rfl⟩ := hφb.2 c
    obtain ⟨x, rfl⟩ := ha.quot.surjective y
    exact ⟨QuotientGroup.mk x⁻¹, by rw [hArt, map_inv art, inv_inv]⟩
  · ext c
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hArt, _root_.GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff ha,
      ← map_one φ, hφb.1.eq_iff, inv_eq_one]
  · intro L h v hv a hsupp
    obtain ⟨x, hx, rfl⟩ := _root_.GlobalTheory.Div.SuppIdele.supported_eq_localIdele hsupp
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω v
    constructor
    · intro hu Q hQ hQv
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.frob v A hA (art (localIdele K v x))).1
        ⟨x, (GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt v x).1 hu, rfl⟩
      rw [hArtσ _ σ (by rw [← hσe, map_inv, inv_inv]), abRestrict_mk]
      exact GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension e L h v A hA σ hσ Q hQ hQv
    · intro hu
      rw [← hx] at hu
      obtain ⟨σ, hσ, hσe⟩ := (ha.ine v A hA (art (localIdele K v x))).1 ⟨x, hu, rfl⟩
      rw [hArtσ _ σ⁻¹ (by rw [← hσe, map_inv]), abRestrict_mk]
      exact GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one e L h v hv A hA σ⁻¹ ((ReciprocityTheory.Gal.Ine A).inv_mem hσ)
  · intro L h w hw
    exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))

theorem periodEx_of_mainTheorem : GlobalTheory.Published.EllipticMainTheoremCM → PeriodEx := by
  intro hMT K _ _ _ ι h2 Λ₀ Ω₀ hΛ hΩ Ω _ _ _ j art hj ha g σ t hσg hsym
  letI : Algebra K ℂ := ι.toAlgebra
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← hj, RingHom.comp_apply, ← hσg, AlgEquiv.commutes]
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨X, hX, ξ, hξ, hT⟩ := exists_uniformisation_torsTransport h2 ι Λ₀ Ω₀ hΛ hΩ
  let e := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  obtain ⟨Art, hArt, hArtσ⟩ := exists_globalArtinMap ha e
  have hjK : ∀ x : K, j (algebraMap K Ω x) = algebraMap K ℂ x := fun x => by
    rw [← RingHom.comp_apply, hj]
    rfl
  let jK : Ω →ₐ[K] ℂ := { j with commutes' := hjK }
  have hR : GlobalTheory.EllipticCM.RestrictsTo gK (Art (QuotientGroup.mk (finIdele K t))) := by
    rw [hArtσ _ σ hsym]
    refine ⟨jK.comp e.symm.toAlgHom, (e.symm.trans σ).trans e, fun x => ?_, rfl⟩
    change g (j (e.symm x)) = j (e.symm (e (σ (e.symm x))))
    rw [AlgEquiv.symm_apply_apply, hσg]
  have hTr := hMT K h2 Art hArt gK (finIdele K t) hR X 1 one_ne_zero ξ hξ
  rw [show GlobalTheory.EllipticCM.finitePart (finIdele K t) = t from GlobalTheory.EllipticCM.finitePart_inr t] at hTr
  exact hT gK t hTr

end GlobalTheory.LatVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → 1 ≤ k → VeryAmpleAt B M k → IsBCBasis B M k bB → GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  first | (exact @GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (exact GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (intros; apply GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestHomMatrixGeneratesNormalisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testHom_matrix_generates_normalised : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c ∧ GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c ∧ GlobalTheory.HomFixUniv.Normal t c αA βB := by
  first | (exact @GlobalTheory.HomFixMatCond.mat_cond) | (exact GlobalTheory.HomFixMatCond.mat_cond) | (intros; apply GlobalTheory.HomFixMatCond.mat_cond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  first | (exact @GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (exact GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (intros; apply GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed  <;> assumption)
end

