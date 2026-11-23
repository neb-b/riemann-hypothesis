module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnHighestWeightPolynomialMap
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

namespace ColHigh

variable {ι : Type} {m n : ℕ}

def der (m : ℕ) (τ : ι) (k l : Fin n) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ i : Fin m, (X (τ, i, k) : Pol ι m n) • pderiv (τ, i, l)

theorem der_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) : der m τ k l P = colLie m τ k l P := by
  have h (S : Finset (Fin m)) (D : Fin m → Derivation ℂ (Pol ι m n) (Pol ι m n)) :
      (∑ i ∈ S, D i) P = ∑ i ∈ S, D i P := by
    rw [← Finset.sum_apply]
    exact congrFun (map_sum Derivation.coeFnAddMonoidHom D S) P
  simp [der, h, colLie_apply]

theorem der_X [DecidableEq ι] (t t' : ι) (k l j : Fin n) (a : Fin m) :
    der m t k l (X (t', a, j)) = if t' = t ∧ j = l then X (t, a, k) else 0 := by
  rw [der_apply, colLie_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [pderiv_X, Pi.single_apply]
  · have (a' : Fin m) : ((t', a, j) : ι × Fin m × Fin n) ≠ (t, a', l) := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [pderiv_X, this]

theorem comm [DecidableEq ι] (t t' : ι) (i k l : Fin n) (P : Pol ι m n) :
    colLie m t i i (colLie m t' k l P) - colLie m t' k l (colLie m t i i P) =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        colLie m t' k l P := by
  have : ⁅der m t i i, der m t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        der m t' k l := by
    refine MvPolynomial.derivation_ext fun ⟨s, a, j⟩ => ?_
    rw [Derivation.commutator_apply, Derivation.smul_apply]
    simp only [der_X, apply_ite (der m t i i), apply_ite (der m t' k l), map_zero]
    by_cases h1 : s = t' ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases h2 : s = t
      · subst h2
        by_cases h3 : i = k <;> by_cases h4 : i = j <;> simp [h3, h4, eq_comm, sub_smul] <;>
          (try split_ifs) <;> simp_all
      · simp [h2, Ne.symm h2]
    · simp only [if_neg h1, smul_zero, zero_sub, neg_eq_zero]
      split_ifs with h2 h3
      · exact absurd ⟨h2.1.trans h3.1, h2.2.trans h3.2⟩ h1
      · rfl
      · rfl
  have := DFunLike.congr_fun this P
  rw [Derivation.commutator_apply, Derivation.smul_apply] at this
  simpa only [der_apply] using this

theorem diag_monomial (t : ι) (k : Fin n) (s : ι × Fin m × Fin n →₀ ℕ) (c : ℂ) :
    colLie m t k k (monomial s c) = ((∑ a, (s (t, a, k) : ℤ) : ℤ) : ℂ) • monomial s c := by
  simp only [colLie_apply, X_mul_pderiv_monomial, Int.cast_sum,
    Int.cast_natCast, Finset.sum_smul, Nat.cast_smul_eq_nsmul]

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (a b : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) : X a * pderiv b P ∈ restrictTotalDegree σ ℂ d := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · rw [mem_restrictTotalDegree] at hP ⊢
    have h1 : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hP
    have h2 : s - Finsupp.single b 1 + Finsupp.single b 1 = s :=
      Finsupp.sub_add_single_one_cancel h
    have h3 : ((s - Finsupp.single b 1).sum fun _ e => e) + 1 = s.sum fun _ e => e := by
      conv_rhs => rw [← h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    refine (totalDegree_mul _ _).trans ?_
    have h4 := totalDegree_monomial_le (s - Finsupp.single b 1) (AddMonoidAlgebra.coeff P s * (s b : ℂ))
    rw [totalDegree_X]
    have h5 : ((s - Finsupp.single b 1).sum fun _ => id) = (s - Finsupp.single b 1).sum fun _ e => e := rfl
    omega

theorem colLie_mem (d : ℕ) (t : ι) (k l : Fin n) (P : Pol ι m n)
    (hP : P ∈ restrictTotalDegree _ ℂ d) : colLie m t k l P ∈ restrictTotalDegree _ ℂ d := by
  rw [colLie_apply]
  exact Submodule.sum_mem _ fun i _ => X_mul_pderiv_mem d _ _ P hP

theorem exists_bound {σ X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (Φ : X →ₗ[ℂ] MvPolynomial σ ℂ) : ∃ d, ∀ x, Φ x ∈ restrictTotalDegree σ ℂ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun i => (Φ (b i)).totalDegree, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_restrictTotalDegree]
  exact Finset.le_sup (f := fun i => (Φ (b i)).totalDegree) (Finset.mem_univ i)

end ColHigh


open ColHigh in
theorem exists_colHighest (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)) (hU0 : U ≠ ⊥)
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) :
    ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧
      ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  classical
  have hL : ∀ τ k l, ∀ Φ ∈ U, colLie m τ k l ∘ₗ Φ ∈ U := by
    intro τ k l Φ hΦ
    obtain ⟨d, hd⟩ := exists_bound Φ
    obtain ⟨s, c, h⟩ := _root_.GlobalTheory.DefLift.colLie_eq_sum_colSub ι m n d τ k l
    have : colLie m τ k l ∘ₗ Φ = ∑ g ∈ s, c g • (colSub m τ g ∘ₗ Φ) := by
      ext1 x
      rw [LinearMap.comp_apply, ← h _ ((mem_restrictTotalDegree _ _ _).1 (hd x))]
      simp [LinearMap.sum_apply]
    rw [this]
    exact U.sum_mem fun g _ => U.smul_mem _ (hU Φ hΦ τ g)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨d, hd⟩ := exists_bound Φ₀
  let R : Submodule ℂ (Pol ι m n) := restrictTotalDegree _ ℂ d
  let B : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range (LinearMap.llcomp ℂ X R _ R.subtype : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n))
  have hB : ∀ Φ, Φ ∈ B ↔ ∀ x, Φ x ∈ R := by
    intro Φ
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  have : FiniteDimensional ℂ B := inferInstance
  have : FiniteDimensional ℂ (U ⊓ B : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_right
  let e : ι → Fin n → Fin n → Module.End ℂ (X →ₗ[ℂ] Pol ι m n) :=
    fun τ k l => LinearMap.llcomp ℂ X _ _ (colLie m τ k l)
  have he : ∀ τ k l Φ, e τ k l Φ = colLie m τ k l ∘ₗ Φ := fun _ _ _ _ => rfl
  obtain ⟨Φ, hΦ, h0, h1, μ, h2⟩ := GlobalTheory.exists_highest_vector e (by
      intro t t' i k l
      refine LinearMap.ext fun Φ => LinearMap.ext fun x => ?_
      exact comm t t' i k l (Φ x))
    (by
      rw [eq_top_iff]
      intro Φ _
      let b := Module.finBasis ℂ X
      have : Φ = ∑ i, ∑ s ∈ (Φ (b i)).support, (b.coord i).smulRight (monomial s (AddMonoidAlgebra.coeff (Φ (b i)) s)) := by
        refine LinearMap.ext fun x => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          conv_lhs => rw [← b.sum_repr x, map_sum]
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, ← Finset.smul_sum, map_smul,
          ← as_sum, Module.Basis.coord_apply]
      rw [this]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun s _ => ?_
      refine Submodule.mem_iSup_of_mem (fun t k => ∑ a, (s (t, a, k) : ℤ)) ?_
      simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro t k
      refine LinearMap.ext fun x => ?_
      rw [he, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        diag_monomial, smul_comm])
    (U ⊓ B) (fun τ k l Φ hΦ => ⟨hL τ k l Φ hΦ.1,
      (hB _).2 fun x => colLie_mem d τ k l _ ((hB _).1 hΦ.2 x)⟩)
    ((Submodule.ne_bot_iff _).2 ⟨Φ₀, ⟨hΦ₀, (hB _).2 hd⟩, hne⟩)
  exact ⟨Φ, hΦ.1, h0, h1, μ, h2⟩

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.LatticeUnitRoot

theorem exists_finUnit_isDetRoot : ∀ (D : D7) (S : HSp D) (Λ : Lt D.host.E S.rank), IsSelfDualC S Λ → ∀ k ∈ GfC S, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) Λ Λ → ∃ x : (AE D)ˣ, FinUnit x ∧ IsDetRoot S k x := by
  intro D V Λ hΛ k hk hm
  have hu : ∀ z ∈ GlobalTheory.Ker.hatV Λ, ∃ y ∈ GlobalTheory.Ker.hatV Λ, (finHom V k).1.mulVec z - z = (1 : ℕ) • y := fun z hz =>
    ⟨_, sub_mem ((hm _).2 ⟨z, hz, rfl⟩) hz, (one_nsmul _).symm⟩
  classical
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F Λ hΛ.1.fg (Submodule.IsFullLattice.span_eq_top (self := hfull V Λ hΛ)) 1 one_ne_zero _ hu
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hw
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

end GlobalTheory.LatticeUnitRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefMapRecord

open Formalism.L2.NTheta

lemma floor_toNat_cast {x : ℚ} (z : ℤ) (hz : x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  subst hz
  rw [Int.floor_intCast]
  have h : 0 ≤ z := by exact_mod_cast h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

lemma lamAt_b {R : Ranks} (h : HCParam R) (n c : ℕ) (hc : c < R.m) (hn : n = R.k - 1 + c) : lamAt h n = -h.b ⟨c, hc⟩ := by
  subst hn
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 3
  omega

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma aPl_cast (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) =
      lamAt (D.hc τ) n + (D.hc τ).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) n
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  rw [aPl, if_pos hn]
  refine floor_toNat_cast (z + e - ((D.R.k + i : ℕ) - (n + 1)) - (s + 1)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
    have h1 := lamAt_add_add_le (D.hc τ) d n (by unfold Ranks.r; omega)
    rw [lamAt_b (D.hc τ) (n + d) i hi (by omega)] at h1
    have h2 := (D.hc τ).gap_be i
    rw [hd]
    push_cast
    simp only [Fin.eta] at h1
    linarith

lemma aMi_cast (q n c : ℕ) (hq : i + 1 + q = D.R.m) (hn : n + c + 1 = q) :
    (aMi D i (D.R.k + i) q τ n : ℚ) =
      -((D.hc τ).e i - (D.hc τ).b ⟨i + 1 + c, by omega⟩ + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i + 1 + c, by omega⟩
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have h0 := lamAt_b (D.hc τ) (D.R.k + i + c) (i + 1 + c) (by omega) (by omega)
  rw [aMi, if_pos (by omega), show q - n = c + 1 by omega, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, h0,
    ← sub_eq_add_neg, Nat.cast_succ]
  refine floor_toNat_cast (-(e - z + (c + 1) + s)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · have h1 := lamAt_add_add_le (D.hc τ) c (D.R.k + i) (by unfold Ranks.r; omega)
    rw [h0, lamAt_b (D.hc τ) (D.R.k + i) (i + 1) (by omega) (by omega)] at h1
    have h2 := (D.hc τ).gap_eb i (by omega)
    linarith

lemma lamV_eq : ∃ s : ℤ, ∀ n : Fin (Vc D i).rank, (lamV D i τ).w n =
    s + (if (n : ℕ) < D.R.k + i then (aPl D i (D.R.k + i) τ n : ℤ) else 0) -
      (if (Fin.rev n : ℕ) < D.R.m - (i + 1) then (aMi D i (D.R.k + i) (D.R.m - (i + 1)) τ (Fin.rev n) : ℤ) else 0) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hW⟩ :=
    GlobalTheory.ForcedWeights.lamLForced D (i + 1) (Nat.le_add_left _ _) hi τ
  have hWe' : (W.e : ℚ) = (D.hc τ).e i := hWe
  have hr : (Vc D i).rank = D.R.k + D.R.m - 1 + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) hi
  obtain ⟨q, hq⟩ : ∃ q, i + 1 + q = D.R.m := ⟨D.R.m - (i + 1), by omega⟩
  have hp : W.p = D.R.k + i := by unfold IndefiniteWeightData.WeightData.p; omega
  have hq' : W.q = q := by unfold IndefiniteWeightData.WeightData.q; omega
  have hnV : W.nV = D.R.k + i + q + D.R.t := by unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; omega
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have ha' : (D.R.k : ℚ) = a + a := by exact_mod_cast ha
  have hb' : (q : ℚ) = b + b - i - 1 := by
    have : ((i : ℕ) : ℚ) + 1 + q = b + b := by exact_mod_cast hq.trans hb
    linarith
  have hd : W.dTau = ((a + (i : ℕ) - b - W.e : ℤ) : ℚ) := by
    unfold IndefiniteWeightData.WeightData.dTau
    rw [hp, hq']
    push_cast
    rw [ha', hb']
    ring
  generalize (a + (i : ℕ) - b - W.e : ℤ) = s at hd
  rw [show D.R.m - (i + 1) = q by omega]
  refine ⟨s, fun n => ?_⟩
  have hn := n.2
  rw [← Int.cast_inj (α := ℚ), hW n, IndefiniteWeightData.WeightData.lamPrime, hd, IndefiniteWeightData.WeightData.thetaWt, hp, hq', hWt, Fin.val_rev,
    Int.cast_sub, Int.cast_add]
  by_cases h1 : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), Int.cast_natCast, aPl_cast D i τ n h1, IndefiniteWeightData.WeightData.aPlus,
      hp, hq', hnV, hWe']
    have hl : (W.lam (n + 1) : ℚ) = lamAt (D.hc τ) n := by
      unfold IndefiniteWeightData.WeightData.lam
      rw [hWk]
      split_ifs with h2
      · rw [lamAt, dite_eq_left (by omega)]
        exact hWv ⟨n, by omega⟩
      · rw [lamAt_b (D.hc τ) n (n - (D.R.k - 1)) (by omega) (by omega), Int.cast_neg,
          show (n : ℕ) + 1 - (D.R.k - 1) = n - (D.R.k - 1) + 1 by omega]
        exact congrArg _ (hWb ⟨n - (D.R.k - 1), by omega⟩)
    rw [hl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (n : ℕ) + 1 ≤ D.R.k + i + D.R.t
    · rw [if_pos h2, if_neg (by omega)]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + D.R.t + c := ⟨n - (D.R.k + i + D.R.t), by omega⟩
      rw [if_neg h2, if_pos (by omega), Int.cast_natCast, aMi_cast D i τ q _ c hq (by omega), IndefiniteWeightData.WeightData.aMinus,
        hq', hWj, hWt, hWe', show q + 1 - (q + 1 - (n + 1 - (D.R.k + i) - D.R.t)) = c + 1 by omega,
        show (i : ℕ) + 1 + (c + 1) = i + 1 + c + 1 by omega, hWb ⟨i + 1 + c, by omega⟩]
      push_cast
      ring

theorem exists_io_record : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  intro D Q hQ κ hκ i c'
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨-, hinj, hΨ, -, hval⟩ := GlobalTheory.WeightExponents.weight_exponents D Q hQ _ (inR i) (κ i)
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ (inR i)
  have hp1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have hq1 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  choose s hs using lamV_eq D i
  refine GlobalTheory.FrameRead.CoefMap.exists_ioLFRec D.host.E Q.H (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank D.what₂.Tau (DV.tauEmb D)
    ⟨hinj, fun τ => (hΨ τ).trans (exists_congr fun _ => eq_comm)⟩ ?_ Q.l c' (wtA (κ i)) s (lamV D i) (dom_wtA (κ i)).1 ?_
  · refine le_trans ?_ (r_le_V i)
    rw [hp, hq, hp1, hq1, Ranks.r]
    omega
  · intro τ n
    have ht := hQ.1.2.2.2 τ
    have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D τ) (Q.H.rt : D.host.E) = Q.H.rt0 :=
      GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 τ
    have hsig : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    obtain ⟨h1, h2, -⟩ := hκ i τ
    rw [hsig] at h1 h2
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos ht, if_neg hc, hp, hq, hs τ n,
      (hval τ _).1, (hval τ _).2]
    congr 1
    · congr 1
      refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), h1]
      rfl
    · refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dite_eq_left (show (Fin.rev n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2 from h), h2]
      rfl

end GlobalTheory.CoefMapRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasDef
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

end GlobalTheory.Mem.DefiniteMeasure
end

