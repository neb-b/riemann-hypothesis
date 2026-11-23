module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0099
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDet
section
open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.IndexDet

theorem relIndex_mul_measure_of_isCompact {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsAddLeftInvariant] {H L : AddSubgroup G} (hL : IsCompact (L : Set G))
    (hH : IsOpen (H : Set G)) (hHL : H ≤ L) :
    (H.relIndex L : ℝ≥0∞) * μ H = μ L := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.addSubgroupOf L : AddSubgroup L) : Set L) := hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  haveI : (H.addSubgroupOf L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact GlobalTheory.BaseModule.addRelIndex_mul_measure H L hHL hH.measurableSet μ

theorem relIndex_eq_distribHaarChar_det_mul (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k)
    (A₀ A : AddSubgroup (Fin n → k)) (hA : IsCompact (A : Set (Fin n → k)))
    (hA₀ : IsOpen (A₀ : Set (Fin n → k))) (h₀ : A₀ ≤ A)
    (h₁ : A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) :
    ((A₀.relIndex A : ℕ) : ℝ) = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) *
      ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  set B := A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom with hB
  let μ : Measure (Fin n → k) := Measure.pi fun _ : Fin n => (Measure.addHaar : Measure k)
  have hBset : (B : Set (Fin n → k)) = (fun x => (g⁻¹).val *ᵥ x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.val *ᵥ x, hx, ?_⟩
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      change g.val *ᵥ ((g⁻¹).val *ᵥ y) ∈ A
      simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec, SetLike.mem_coe] using hy
  have hBc : IsCompact (B : Set (Fin n → k)) := by
    rw [hBset]
    exact hA.image (by fun_prop)
  have hAm : MeasurableSet (A : Set (Fin n → k)) := hA.measurableSet
  have hm : Measurable (g.val.mulVec) := (continuous_const.matrix_mulVec continuous_id).measurable
  have hscale : μ A = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * μ B := by
    have h := GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure k) g.val
      (Matrix.GeneralLinearGroup.det g) rfl
    have h2 := congrArg (fun m : Measure (Fin n → k) => m (A : Set (Fin n → k))) h
    simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hAm] at h2
    exact h2.symm
  have i1 := relIndex_mul_measure_of_isCompact μ hA hA₀ h₀
  have i2 := relIndex_mul_measure_of_isCompact μ hBc hA₀ h₁
  have hpos : μ A₀ ≠ 0 := (hA₀.measure_pos μ ⟨0, A₀.zero_mem⟩).ne'
  have htop : μ A₀ ≠ ∞ := ((measure_mono h₀).trans_lt hA.measure_lt_top).ne
  have key : ((A₀.relIndex A : ℕ) : ℝ≥0∞) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * ((A₀.relIndex B : ℕ) : ℝ≥0∞) := by
    refine (ENNReal.mul_left_inj hpos htop).mp ?_
    rw [i1, hscale, ← i2, mul_assoc]
  have := congrArg ENNReal.toReal key
  simpa using this

end GlobalTheory.CompanionTheory.IndexDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexFlipIsomorphism
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.DCFlip

variable {R : Type} [CommRing R]

def sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : ∀ q p, K.flip.X q p :=
  fun q p => (-1 : ℤ) ^ (p * q) • x p q

theorem sw_apply (K : DCx.{w} R) (x : ∀ p q, K.X p q) (q p : ℕ) :
    sw K x q p = (-1 : ℤ) ^ (p * q) • x p q := rfl

theorem neg_one_pow_eq_of_even {m n : ℕ} (h : Even (m + n)) : (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  have hm : (-1 : ℤ) ^ m * (-1 : ℤ) ^ n = 1 := by rw [← pow_add]; exact h.neg_one_pow
  have hn : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
  exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0)) (hm.trans hn.symm)

theorem sign_smul_sign_smul {M : Type w} [AddCommGroup M] (k : ℕ) (z : M) :
    (-1 : ℤ) ^ k • (-1 : ℤ) ^ k • z = z := by
  rw [smul_smul, ← mul_pow]; simp

theorem D_sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : K.flip.D (sw K x) = sw K (K.D x) := by
  funext a b
  rcases a with _ | a <;> rcases b with _ | b
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · have e1 : (-1 : ℤ) ^ ((b + 1) * a) = (-1 : ℤ) ^ ((b + 1) * (a + 1) + (b + 1)) :=
      neg_one_pow_eq_of_even ⟨(b + 1) * a + (b + 1), by ring⟩
    have e2 : (-1 : ℤ) ^ (a + 1 + b * (a + 1)) = (-1 : ℤ) ^ ((b + 1) * (a + 1)) := by
      congr 1; ring
    simp only [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply, map_zsmul, smul_add, smul_smul, ← pow_add]
    rw [e1, e2]
    exact add_comm _ _

def swHom (K : DCx.{w} R) : Cx.Hom K.tot K.flip.tot (RingHom.id R) where
  f n :=
    { toFun := fun x => ⟨sw K x.1, fun q p h => by
        change (-1 : ℤ) ^ (p * q) • x.1 p q = 0
        rw [x.2 p q (by omega), smul_zero]⟩
      map_add' := fun x y => Subtype.ext (funext fun q => funext fun p =>
        smul_add ((-1 : ℤ) ^ (p * q)) (x.1 p q) (y.1 p q))
      map_smul' := fun c x => Subtype.ext (funext fun q => funext fun p =>
        smul_comm ((-1 : ℤ) ^ (p * q)) c (x.1 p q)) }
  comm n x := Subtype.ext (D_sw K x.1)

theorem flip_tot : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  intro R _ K
  refine ⟨swHom K, fun n => ⟨fun x y h => ?_, fun y => ?_⟩, fun n x p q => rfl⟩
  · refine Subtype.ext (funext fun p => funext fun q => ?_)
    have h' : (-1 : ℤ) ^ (p * q) • x.1 p q = (-1 : ℤ) ^ (p * q) • y.1 p q :=
      congrFun (congrFun (congrArg Subtype.val h) q) p
    have h'' := congrArg (fun z => (-1 : ℤ) ^ (p * q) • z) h'
    simpa only [sign_smul_sign_smul] using h''
  · refine ⟨⟨fun p q => (-1 : ℤ) ^ (p * q) • y.1 q p, fun p q h => ?_⟩, ?_⟩
    · change (-1 : ℤ) ^ (p * q) • y.1 q p = 0
      rw [y.2 q p (by omega), smul_zero]
    · refine Subtype.ext (funext fun q => funext fun p => ?_)
      exact sign_smul_sign_smul (p * q) (y.1 q p)

end GlobalTheory.CompanionTheory.DCFlip
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem support_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (Ainf F))
    (hK : IsCompact K) (Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hKv : ∀ v ∈ T, IsCompact (Kv v))
    (δ : ℝ) (hδ : 0 < δ) :
    {x : F | x ≠ 0 ∧ x ∈ IntOut T ∧ θ δ * algebraMap F (Ainf F) x ∈ K ∧
      ∀ v ∈ T, algebraMap F (Fv F v) x ∈ Kv v}.Finite := by
  obtain ⟨N, hN, hNx⟩ := _root_.GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator F T Kv hKv
  obtain ⟨C0, h⟩ := hC F hF θ hθ K hK N hN
  refine ((h δ hδ ⊤ top_ne_bot).1).subset ?_
  rintro x ⟨h0, h1, h2, h3⟩
  obtain ⟨y, hy⟩ := hNx x h1 h3
  exact ⟨h0, ⟨y, Submodule.mem_top, hy⟩, h2⟩

theorem tsum_ne_zero_eq_sum {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ x ∈ B, h x := by
  have h1 : ∑' β : {β : F // β ≠ 0}, h β.1 = ∑ β ∈ B.subtype (fun x => x ≠ 0), h β.1 := by
    refine tsum_eq_sum ?_
    intro b hb
    exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)
  rw [h1]
  refine Finset.sum_bij (fun b _ => b.1) ?_ ?_ ?_ ?_
  · intro a ha; simpa [Finset.mem_subtype] using ha
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb; exact ⟨⟨b, hB b hb⟩, by simpa [Finset.mem_subtype] using hb, rfl⟩
  · intro a _; rfl

theorem truncTerm_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Finset F, (∀ x ∈ B, x ≠ 0) ∧ ∀ x, x ≠ 0 → x ∉ B → (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) x = 0 := by
  have hfin := support_finite hC F hF θ hθ T (tsupport G) hGc (fun v => tsupport (ψ v)) hψ δ hδ
  refine ⟨hfin.toFinset, fun x hx => ((hfin.mem_toFinset).1 hx).1, ?_⟩
  intro x hx0 hxB
  by_cases hxT : x ∈ IntOut T
  · rw [Set.indicator_of_mem hxT]
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · have : ∃ v ∈ T, algebraMap F (Fv F v) x ∉ tsupport (ψ v) := by
        by_contra hcon
        push_neg at hcon
        exact hxB ((hfin.mem_toFinset).2 ⟨hx0, hxT, h1, hcon⟩)
      obtain ⟨v, hv, hvx⟩ := this
      have h0 : ψ v (algebraMap F (Fv F v) x) = 0 := image_eq_zero_of_notMem_tsupport hvx
      rw [Finset.prod_eq_zero hv h0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · exact Set.indicator_of_notMem hxT _

theorem truncTerm_summable (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hGc : HasCompactSupport G)
    (hψ : ∀ v ∈ T, HasCompactSupport (ψ v)) (δ : ℝ) (hδ : 0 < δ) :
    Summable fun β : {β : F // β ≠ 0} => (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1 := by
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc hψ δ hδ
  refine summable_of_ne_finset_zero (s := B.subtype (fun x => x ≠ 0)) ?_
  intro b hb
  exact hh b.1 b.2 (by simpa [Finset.mem_subtype] using hb)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

noncomputable section
namespace GlobalTheory.CompanionTheory.TubeFourier

theorem continuous_pt (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  have h : (fun y : ℝ × ℝ => pt x y) =
      fun y => ((x.1 : ℂ) + (y.1 : ℂ) * Complex.I, (x.2 : ℂ) + (y.2 : ℂ) * Complex.I) := by
    funext y
    simp [pt, Complex.ext_iff]
  rw [h]
  fun_prop

theorem pt_re_im (l : ℂ × ℂ) : pt (l.1.re, l.2.re) (l.1.im, l.2.im) = l := by
  exact Prod.ext (Complex.eta _) (Complex.eta _)

private lemma pt_mem_tube_iff {x y : ℝ × ℝ} {S : Set (ℝ × ℝ)} : pt x y ∈ tube S ↔ x ∈ S := by
  simp [tube, pt]

theorem tubeChain : TubeChain := by
  intro X _ _ _ T _ _ m Ω F hΩ hV hmid
  set G : Fin (m + 1) → T → ℂ × ℂ → X := fun i g => gauss (F i · g) with hGdef
  have hGT : ∀ i g, GaussTube (G i g) (Ω i) := fun i g => gaussTube_of_tubeGood (hΩ i).2.2 g
  have hind : ∀ i g, ∀ x ∈ Ω i, ∀ x' ∈ Ω i, ∀ t, phi (G i g) x t = phi (G i g) x' t :=
    fun i g => _root_.GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex X (Ω i) (G i g) (hΩ i).1 (hΩ i).2.1 (hGT i g)
  have hstep : ∀ i : Fin m, ∀ g, ∀ x ∈ Ω i.castSucc, ∀ x' ∈ Ω i.succ, ∀ t,
      phi (G i.castSucc g) x t = phi (G i.succ g) x' t := by
    intro i g x hx x' hx' t
    obtain ⟨V, -, ⟨v, hv⟩, hVsub, hVeq⟩ := hV i
    rw [hind _ g x hx v (hVsub hv).1, hind _ g x' hx' v (hVsub hv).2]
    unfold phi
    congr 1
    funext y
    congr 1
    simp only [G, gauss]
    rw [hVeq (pt v y) (pt_mem_tube_iff.2 hv) g]
  have hQ : ∀ g t, ∀ k : Fin (m + 1), ∀ x ∈ Ω 0, ∀ x' ∈ Ω k,
      phi (G 0 g) x t = phi (G k g) x' t := by
    intro g t k
    induction k using Fin.induction with
    | zero => exact fun x hx x' hx' => hind 0 g x hx x' hx' t
    | succ i ih =>
      intro x hx x' hx'
      obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV i
      rw [ih x hx v (hVsub hv).1]
      exact hstep i g v (hVsub hv).1 x' hx' t
  have hne0 : (Ω 0).Nonempty := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      obtain ⟨i, j, a, ha, b, hb, -⟩ := hmid 0
      obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.isLt)
      exact ⟨a, ha⟩
    · obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV ⟨0, hm⟩
      have h0 : (Fin.castSucc (⟨0, hm⟩ : Fin m)) = 0 := by
        ext
        simp
      exact ⟨v, h0 ▸ (hVsub hv).1⟩
  obtain ⟨x0, hx0⟩ := hne0
  set φ : ℝ × ℝ → T → X := fun t g => phi (G 0 g) x0 t with hφdef
  have hall : ∀ i g, ∀ x ∈ Ω i, ∀ t, phi (G i g) x t = φ t g :=
    fun i g x hx t => (hQ g t i x0 hx0 x hx).symm
  have hGcont : ∀ i, ∀ x ∈ Ω i, Continuous (fun p : (ℝ × ℝ) × T => G i p.2 (pt x p.1)) := by
    intro i x hx
    have hp : Continuous fun p : (ℝ × ℝ) × T => pt x p.1 := (continuous_pt x).comp continuous_fst
    have h1 : Continuous (fun p : (ℝ × ℝ) × T => F i (pt x p.1) p.2) := by
      refine (hΩ i).2.2.cont.comp_continuous (hp.prodMk continuous_snd) ?_
      intro p
      exact ⟨pt_mem_tube_iff.2 hx, Set.mem_univ _⟩
    have he : Continuous fun p : (ℝ × ℝ) × T =>
        Complex.exp ((pt x p.1).1 ^ 2 + (pt x p.1).2 ^ 2) :=
      Complex.continuous_exp.comp (((continuous_fst.comp hp).pow 2).add ((continuous_snd.comp hp).pow 2))
    exact he.smul h1
  have hGbd : ∀ i, ∀ x ∈ Ω i, ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G i g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
    intro i x hx g
    obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 (Set.singleton_subset_iff.2 hx)
      isCompact_singleton g
    refine ⟨U, hU, M, fun g' hg' y => ?_⟩
    have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 rfl)
    simpa [pt] using this
  have hφcont : Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) :=
    GlobalTheory.T.gaussian_tube_transform_continuous X T (G 0) x0 (hGcont 0 x0 hx0) (fun g => hGbd 0 x0 hx0 g)
  have hφt : ∀ g : T, Continuous fun t => φ t g := fun g =>
    hφcont.comp (show Continuous (fun t : ℝ × ℝ => (t, g)) by fun_prop)
  have hdecay : ExpDecay φ := by
    refine _root_.GlobalTheory.CompanionTheory.TubeFourier.expDecay_of_midpoint X T φ {a | ∃ i, a ∈ Ω i} ?_ ?_
    · rintro a ⟨i, ha⟩ g
      obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ((hΩ i).1.mem_nhds ha)
      obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 hsub (isCompact_closedBall a r) g
      refine ⟨r, hr, U, hU, M * Real.pi, fun x hx1 hx2 g' hg' t => ?_⟩
      have hxC : x ∈ Metric.closedBall a r := by
        rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
        exact ⟨hx1, hx2⟩
      rw [← hall i g' x (hsub hxC) t]
      refine _root_.GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le X (G i g') x M (fun y => ?_) t
      have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 hxC)
      simpa [pt] using this
    · intro x
      obtain ⟨i, j, a, ha, b, hb, hx⟩ := hmid x
      exact ⟨a, ⟨i, ha⟩, b, ⟨j, hb⟩, hx⟩
  refine ⟨fun l g => inv (fun t => φ t g) l, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v
    exact (_root_.GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line X T φ hdecay hφt g p v).differentiableOn
  · exact (_root_.GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint X T φ hdecay hφcont).continuousOn
  · intro C _ hC g
    obtain ⟨U, hU, M, hM⟩ := _root_.GlobalTheory.CompanionTheory.TubeFourier.inv_bounded_on_tube X T φ hdecay hφt C hC g
    exact ⟨U, hU, M, fun l hl g' hg' => hM l hl g' hg'⟩
  · intro i l hl g
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ × ℝ, x = (l.1.re, l.2.re) := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y : ℝ × ℝ, y = (l.1.im, l.2.im) := ⟨_, rfl⟩
    have hx : x ∈ Ω i := hxdef ▸ hl
    have hphi : phi (G i g) x = fun t => φ t g := funext fun t => hall i g x hx t
    have hc1 : Continuous fun y' : ℝ × ℝ => G i g (pt x y') := by
      have h := (hGcont i x hx).comp (show Continuous (fun y' : ℝ × ℝ => (y', g)) by fun_prop)
      simpa only [Function.comp_def] using h
    obtain ⟨U, hU, M, hM⟩ := hGbd i x hx g
    obtain ⟨ε, hε, U', hU', M', hM'⟩ := hdecay x g
    have key := _root_.GlobalTheory.CompanionTheory.TubeFourier.PhiInv.inv_phi_eq X (G i g) x hc1 ⟨M, fun y' => hM g (mem_of_mem_nhds hU) y'⟩
      (by rw [hphi]; exact hφt g)
      ⟨ε, hε, M', fun t => by
        rw [hall i g x hx t]
        exact hM' x (by simp [hε.le]) (by simp [hε.le]) g (mem_of_mem_nhds hU') t⟩ y
    rw [hphi, hxdef, hydef, pt_re_im] at key
    simpa [G, gauss] using key

end GlobalTheory.CompanionTheory.TubeFourier
end
end

