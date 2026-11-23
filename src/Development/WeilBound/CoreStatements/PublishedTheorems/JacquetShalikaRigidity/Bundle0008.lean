module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.NormAverageBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace NormAverageBound

theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, ‖Φ x‖ ≤ C) : ‖avg Γ Φ‖ ≤ C := by
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with hex
  · obtain ⟨-, -, h1⟩ := hex.choose_spec
    have hfin : hex.choose.1 hex.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    calc ‖∫ x in hex.choose.2, Φ x ∂hex.choose.1‖ ≤ C * hex.choose.1.real hex.choose.2 :=
          norm_setIntegral_le_of_norm_le_const hfin (fun x _ => h x)
      _ = C := by simp [Measure.real, h1]
  · simpa using hC

end NormAverageBound

open NormAverageBound in
theorem fourier_column_of : N0 → P0 → P1 → CornerEmbedding → FourierSeriesColumn := by
  intro hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g
  obtain ⟨hFc, hFl, hFlaw, hFvan⟩ := hF
  have hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F := ⟨hFc, hFl, hFlaw⟩
  obtain ⟨hcolPre, hcoef, -, -⟩ := hP1 E m ψ hψ k hk hkm F hPre
  obtain ⟨-, hcolL, -⟩ := hcolPre
  obtain ⟨hgamM, huniqM, -⟩ := hN0 E m k hk hkm.le
  obtain ⟨hgamK, -⟩ := hN0 E k k hk le_rfl
  obtain ⟨hex, hprops⟩ := hK5e E m k hkm.le
  obtain ⟨ιE, hιE⟩ := hex E
  obtain ⟨-, -, -, -, -, -, hrat, -⟩ := hprops ι hι
  have hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m,
      Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0 := by
    intro ρ
    refine ⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩,
      fun i => rfl⟩
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 (Subtype.property ρ).1
      intro h0
      apply hc
      have h1 := congrFun h0 ⟨c, lt_trans c.isLt hkm⟩
      simpa [c.isLt] using h1
    · intro i hi
      simp [show ¬ (i : ℕ) < k by omega]
  choose lift hlift using hlift
  have hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) =
      colT ψ k F (ι (ratGL E k (gam ρ) * g)) := by
    intro ρ
    rw [hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]
    have hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ)) := by
      intro i c hic
      rw [hιE (gam ρ)]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      rw [dite_eq_right (by omega)]
    obtain ⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩ := huniqM _ hBlk
    have hξ : ξ'' = lift ρ := by
      apply Subtype.ext
      funext c
      have hrow := congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ
      simp only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow
      have hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l =
          (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l := fun l => hp _ _ (Or.inl le_rfl)
      simp only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hrow
      rw [(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)] at hrow
      rw [← hrow, hlift ρ c]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      by_cases hc : (c : ℕ) < k
      · rw [dite_eq_left ⟨by show k - 1 < k; omega, hc⟩, dite_eq_left hc]
        exact (hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)
      · rw [dite_eq_right (fun h => hc h.2), dite_eq_right hc, Matrix.one_apply, if_neg]
        intro h
        apply hc
        rw [← h]
        show k - 1 < k
        omega
    rw [hγ, map_mul, mul_assoc, hcolL p hp, hξ]
  have hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0 := by
    have h0 := hFvan k (by omega) le_rfl (ι g)
    simpa [GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot] using h0
  have hinj : Function.Injective
      (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) := by
    intro ρ₁ ρ₂ h
    apply Subtype.ext
    funext j
    have h1 := congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m))
      ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)
    beta_reduce at h1
    rw [hlift, hlift, dite_eq_left j.isLt, dite_eq_left j.isLt] at h1
    exact h1
  have hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m),
      (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show ((Subtype.val t).2 : ℕ) = k
      have h2 := Subtype.property t
      omega
  have hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k,
      (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c := by
    intro c hc
    obtain ⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j =
        c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ :
          UnipotentBlockColumnIndex m k k) := by
      refine ⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m),
        (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k))
        ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩
      intro h0
      apply hc
      funext t
      rw [hkey t]
      exact congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩
    refine ⟨ρ, ?_⟩
    funext t
    show Subtype.val (lift ρ) (Subtype.val t).1 = c t
    rw [hlift, dite_eq_left (Subtype.property t).1, hρ]
    exact congrArg c (hkey t).symm
  have hoff : ∀ c : UnipotentBlockColumnIndex m k k → E,
      c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) →
        coefF ψ k c F (ι g) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact hcoef0
    · exact absurd (hsurj c hc0) (fun h => hc h)
  have hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g)) :=
    per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)
  obtain ⟨-, hP0b, hP0c⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)
  refine ⟨?_, ?_⟩
  · intro B hB
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
        (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))) :=
      hP0b _ _ hper hper
    have hS := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
      (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar
    have hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2 :=
      norm_avg_le _ _ _ (sq_nonneg B) (fun x => by
        simpa [norm_mul, sq] using mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)
    have hre := ((Complex.hasSum_iff _ _).1 hS).1
    simp only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre
    simp only [Complex.mul_conj] at hSle
    have hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 =
        ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := by
      intro ρ
      rw [hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]
    calc ∑' ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2
        = ∑' ρ : RowT E k k, ENNReal.ofReal (Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' ρ : RowT E k k, Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Complex.normSq_nonneg _) hre.summable).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          rw [hre.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)
  · intro hfin
    have hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite := by
      refine (hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc hcoef0
      obtain ⟨ρ, rfl⟩ := hsurj c hc0
      refine ⟨ρ, ?_, rfl⟩
      show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0
      rw [← hA ρ]
      exact hc
    have hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g)) :=
      hP0c _ hper hfin'
    have hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1 := by
      unfold GlobalTheory.CuspGeneric.blkU
      exact GlobalTheory.CuspGeneric.posU_zero _
    rw [hb0, one_mul] at hs
    have hs2 := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs
    show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)
    rw [← hs2.tsum_eq]
    exact tsum_congr fun ρ => (hA ρ).symm

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PoissonCutoffAlgebra
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PoissonCutoffAlgebra

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem exists_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)⟩⟩

theorem psi_nontriv {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : ∃ a : Ad E, ψ a ≠ 1 := by
  obtain ⟨w⟩ := exists_pl (E := E)
  obtain ⟨y, hy⟩ := hψ.loc w
  exact ⟨_, hy⟩

theorem alg_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Function.Injective (algebraMap E (Ad E)) := by
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  haveI : Nontrivial (Ad E) := ⟨⟨a, 0, fun h => ha (by rw [h, AddChar.map_zero_eq_one])⟩⟩
  exact (algebraMap E (Ad E)).injective

noncomputable def eL (hi : Function.Injective (algebraMap E (Ad E))) : (Fin k → E) ≃ vecLattice E (Fin k) :=
  Equiv.ofBijective (fun ξ => ⟨fun i => algebraMap E (Ad E) (ξ i), ξ, rfl⟩)
    ⟨fun a b h => funext fun i => hi (congrFun (congrArg Subtype.val h) i),
     fun γ => by obtain ⟨ξ, hξ⟩ := γ.2; exact ⟨ξ, Subtype.ext hξ⟩⟩

theorem eL_val (hi : Function.Injective (algebraMap E (Ad E))) (ξ : Fin k → E) :
    ((eL hi ξ : vecLattice E (Fin k)) : Fin k → Ad E) = fun i => algebraMap E (Ad E) (ξ i) := rfl

def B (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : ℂ := ψ (∑ i, x i * y i)

theorem B_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (y : Fin k → Ad E) : Continuous fun x => B ψ x y :=
  hψ.cont.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)

theorem B_symm (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : B ψ x y = B ψ y x := by
  simp only [B, mul_comm]

theorem B_add (ψ : AddChar (Ad E) ℂ) (x x' y : Fin k → Ad E) : B ψ (x + x') y = B ψ x y * B ψ x' y := by
  simp only [B, ← AddChar.map_add_eq_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem B_ker {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : Fin k → Ad E) :
    (∀ γ ∈ vecLattice E (Fin k), B ψ γ x = 1) ↔ x ∈ vecLattice E (Fin k) := by
  classical
  constructor
  · intro h
    have : ∀ i, ∃ d : E, x i = algebraMap E (Ad E) d := by
      intro i
      refine hψ.ann (x i) fun c => ?_
      have := h (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) (algebraMap_mem_vecLattice _)
      have e : (∑ j, (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) j * x j) =
          x i * algebraMap E (Ad E) c := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp [mul_comm]
      simp only [B] at this
      rwa [e] at this
    choose d hd using this
    exact ⟨d, funext fun i => (hd i).symm⟩
  · rintro ⟨d, rfl⟩ γ ⟨ξ, rfl⟩
    have : (∑ i, (fun i => algebraMap E (Ad E) (ξ i)) i * (fun i => algebraMap E (Ad E) (d i)) i) =
        algebraMap E (Ad E) (∑ i, ξ i * d i) := by simp [map_sum, map_mul]
    simp only [B]
    exact this ▸ hψ.rat _

theorem B_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (γ : Fin k → Ad E) (hγ : γ ∈ vecLattice E (Fin k))
    (h : ∀ x, B ψ γ x = 1) : γ = 0 := by
  classical
  obtain ⟨ξ, hξ⟩ := hγ
  have hξ' : γ = fun i => algebraMap E (Ad E) (ξ i) := hξ.symm
  subst hξ'
  by_contra hne
  have : ∃ i, ξ i ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hne (funext fun i => by simp [h0 i])
  obtain ⟨i, hi⟩ := this
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  apply ha
  have := h (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E)
  have e : (∑ j, (fun j => algebraMap E (Ad E) (ξ j)) j * (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E) j) = a := by
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  simp only [B] at this
  rwa [e] at this

noncomputable def T (g : GA E k) : (Fin k → Ad E) ≃ₜ (Fin k → Ad E) where
  toFun x := x ᵥ* g.val
  invFun x := x ᵥ* g⁻¹.val
  left_inv x := by simp [Matrix.vecMul_vecMul]
  right_inv x := by simp [Matrix.vecMul_vecMul]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

theorem cov (hD : D0) (hM : AdelicLinearChange) (g : GA E k) (h : (Fin k → Ad E) → ℂ) :
    ∫ x, h (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ((Dt g)⁻¹ : ℝ) • ∫ y, h y ∂vecMeasure E (Fin k) := by
  have hpos : 0 < Dt g := (hD E k).1 g
  have hmap : Measure.map (T g) (vecMeasure E (Fin k)) = ENNReal.ofReal (Dt g)⁻¹ • vecMeasure E (Fin k) := by
    ext A hA
    rw [Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
      lintegral_map (measurable_one.indicator hA) (T g).continuous.measurable]
    exact (hM E k g (A.indicator 1) (measurable_one.indicator hA)).2
  have := integral_map_equiv (T g).toMeasurableEquiv h (μ := vecMeasure E (Fin k))
  rw [Homeomorph.toMeasurableEquiv_coe, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hpos.le)] at this
  exact this.symm

def eR : RowT E k k ≃ {ξ : Fin k → E // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1, ξ.2.1⟩
  invFun ξ := ⟨ξ.1, ξ.2, fun i hi => absurd hi (not_le.2 i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Ps (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k) (y : Fin k → Ad E) : ℂ :=
  (η y : ℂ) * φ (g * (s y)⁻¹)

def Jf (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k)
    (ξ : Fin k → E) : ℂ :=
  ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)
    ∂vecMeasure E (Fin k)

theorem alg_zero : (fun i => algebraMap E (Ad E) ((0 : Fin k → E) i)) = 0 := by
  ext i; simp

theorem stepA (hD : D0) (hM : AdelicLinearChange) (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k)
    (φ : XB E k) (g : GA E k) (ξ : Fin k → E) :
    ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x (fun i => algebraMap E (Ad E) (ξ i)) ∂vecMeasure E (Fin k) =
      ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
  have e := cov hD hM g (fun y => (η y : ℂ) * φ (g * (s y)⁻¹) *
    ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i))
  refine Eq.trans ?_ e
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Ps, B]
  congr 2
  change x ⬝ᵥ _ = (x ᵥ* g.val) ⬝ᵥ (_ ᵥ* (g⁻¹.val)ᵀ)
  rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  simp

end PoissonCutoffAlgebra

open PoissonCutoffAlgebra in
theorem poisson_cutoff_of : D0 → AdelicLinearChange → N0 → H0 → ThetaSeriesBound → K1 → PoissonCutoffFormula := by
  intro hD hM hN _hH hG hK E _ _ _ k hk ψ hψ S U φ η s hcut hinv g
  classical
  have hi := alg_inj hψ
  have hDpos : ∀ h : GA E k, 0 < Dt h := (hD E k).1
  have hΨc : Continuous (Ps η s φ g) := by
    have := (continuous_eval_const g).comp hcut.contV
    refine this.congr fun y => ?_
    simp [Rt_apply, Ps]
  have hΨs : HasCompactSupport (Ps η s φ g) := by
    have : HasCompactSupport fun y => (η y : ℂ) := hcut.cpt.comp_left Complex.ofReal_zero
    exact this.mul_right
  have hΨ0 : Ps η s φ g 0 = 0 := by simp [Ps, hcut.zero]
  have hfc : Continuous fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨc.comp (T g).continuous
  have hfs : HasCompactSupport fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨs.comp_homeomorph (T g)

  obtain ⟨Cf, hCf, hft⟩ := hcut.ft
  obtain ⟨M, C0, hG3⟩ := hG E k Cf hCf k le_rfl
  obtain ⟨C, hC⟩ := hft M
  obtain ⟨-, hdpos, hdle, -⟩ := hK E k hk
  have hp : 0 < Dt (invT g) ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos (hDpos _) _
  have hr : 0 < dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) := mul_pos (hdpos _) hp
  have hrle : ∀ ξ : Fin k → E, ξ ≠ 0 → dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) ≤ height (invT g) ξ := by
    intro ξ hξ
    have := hdle (invT g) ξ hξ
    rwa [ht, le_div_iff₀ hp] at this
  have hsumG := hG3 (invT g) _ hr hrle
  have hu0 : ∀ ξ : Fin k → E, 0 ≤ Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := fun ξ =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (pow_nonneg (by positivity) _)) _
  have hus : Summable fun ξ : Fin k → E => Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := by
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumG
    have h1 := (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (hu0 ξ.1)
    exact (Set.finite_singleton (0 : Fin k → E)).summable_compl_iff.1 h1
  have hJs : Summable fun ξ => ‖Jf ψ η s φ g ξ‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _ g).trans (le_of_eq ?_)) (hus.mul_left C)
    by_cases hx : (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) ∈ Cf <;> simp [hx]
  have hsumΓ : Summable fun γ : vecLattice E (Fin k) =>
      ‖∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)‖ := by
    refine (eL hi).summable_iff.1 ((hJs.mul_left (Dt g)⁻¹).congr fun ξ => ?_)
    rw [Function.comp_apply, eL_val, stepA hD hM, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hDpos g))]

  obtain ⟨hdisc, K, hK, hcov⟩ := isCoLat_ratV E (Fin k)
  haveI : DiscreteTopology (vecLattice E (Fin k)) := hdisc
  have hP := GlobalTheory.CovolumeOneSelfDual.poisson (vecLattice E (Fin k)) K hK hcov (B ψ) (B_cont hψ) (B_symm ψ)
    (B_add ψ) (fun x y => hψ.norm _) (B_ker hψ) (fun γ hγ h => B_inj hψ γ hγ h) (vecMeasure E (Fin k))
    (vecDomain E (Fin k)) isAddFundamentalDomain_vecDomain vecMeasure_vecDomain hfc hfs hsumΓ
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  have hL : sumF (fun h => (η (lastRow h) : ℂ) * φ (h * (s (lastRow h))⁻¹)) g =
      ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) := by
    unfold sumF
    rw [← (eR (E := E) (k := k)).symm.tsum_eq]
    rw [← tsum_subtype_eq_of_support_subset (s := {ξ : Fin k → E | ξ ≠ 0})]
    · refine tsum_congr fun ξ => ?_
      beta_reduce
      rw [hlast, mul_assoc, hinv (gam (eR.symm ξ))]
      rfl
    · intro ξ hξ
      simp only [Set.mem_setOf_eq]
      rintro rfl
      apply hξ
      simp only [alg_zero, Matrix.zero_vecMul, hΨ0]
  have hR : ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) =
      ∑' ξ : Fin k → E, ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
    have h1 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) => Ps η s φ g ((γ : Fin k → Ad E) ᵥ* g.val)
    have h2 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) =>
      ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)
    simp only [eL_val] at h1 h2
    rw [h1, hP, ← h2]
    exact tsum_congr fun ξ => stepA hD hM ψ η s φ g ξ
  have hJsum : Summable (Jf ψ η s φ g) := hJs.of_norm
  have hJ0 : Jf ψ η s φ g 0 = ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k) := by
    rw [Jf, alg_zero]
    simp
  rw [hL, hR]
  simp only [Complex.real_smul, tsum_mul_left, Complex.ofReal_inv]
  rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 (hDpos g).ne'),
    ← hJsum.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton, hJ0]
  rfl

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VectorMeasureTranspose
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
end

