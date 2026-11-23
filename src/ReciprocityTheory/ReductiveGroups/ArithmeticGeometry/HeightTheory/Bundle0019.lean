module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GenericPointHeight.GenericPointStatements.GenericPointTheorem.HtGenericPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisBlock0
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem basis_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) (Q0 : KTp K d.D d.N)
      (M : Fin (d.N + 1) → Matrix (Fin n) (Fin n) (KTp K d.D d.N)),
      Q0 ≠ 0 ∧ (∀ x, d.sub0 x Q0 = Q0) ∧ (∀ j a a' x, d.sub0 x (M j a a') = M j a a') ∧
      ∀ j, Algebra.leftMulMatrix b (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
          (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) =
        (M j).map fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q /
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q0 := by
  letI _inst : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨L, E, _, _, _, _, eL, eE, hcomp, hconst, hLc⟩ := d.decomp_block0 hd h c
  letI iLY : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) E)) :=
    (VariableBasisExtension.liftY (L := L) (E := E) (σ := Fin (d.N + 1))).toAlgebra
  obtain ⟨b', _, hb'2⟩ := VariableBasisExtension.basis_extend (σ := Fin (d.N + 1)) (Module.finBasis L E)
  letI iFO : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (OmS (Ω c) d.D d.N) :=
    ((d.KTtoS h c).comp eL.symm.toRingHom).toAlgebra
  have hback : ∀ q : FractionRing (MvPolynomial (Fin (d.N + 1)) L),
      eE.symm (VariableBasisExtension.liftY q) = d.KTtoS h c (eL.symm q) := by
    intro q
    have h1 := hcomp (eL.symm q)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [← h1, RingEquiv.symm_apply_apply]
  let eEl : FractionRing (MvPolynomial (Fin (d.N + 1)) E) ≃ₗ[FractionRing (MvPolynomial (Fin (d.N + 1)) L)]
      OmS (Ω c) d.D d.N :=
    AddEquiv.toLinearEquiv eE.symm.toAddEquiv (by
      intro q x
      show eE.symm (q • x) = q • eE.symm x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact hback q)
  let B0 := b'.map eEl
  let B : Module.Basis (Fin (Module.finrank L E)) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    B0.mapCoeffs eL.symm (fun q x => rfl)
  have htr : ∀ (y : OmS (Ω c) d.D d.N) a a', Algebra.leftMulMatrix B y a a' =
      eL.symm (Algebra.leftMulMatrix b' (eE y) a a') := by
    intro y a a'
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    have hy : eEl.symm (y * eEl (b' a')) = eE y * b' a' := by
      show eE (y * eE.symm (b' a')) = eE y * b' a'
      rw [map_mul, RingEquiv.apply_symm_apply]
    simp only [B]
    erw [Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr]
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, Finsupp.mapRange.linearEquiv_apply,
      Finsupp.mapRange_apply, B0, Module.Basis.map_apply, Module.Basis.map_repr]
    rw [hy]
    exact rfl
  choose e he using hconst
  choose P Q hQ hPinv hQinv hPQ using hLc
  let mm : Fin (d.N + 1) × Fin (Module.finrank L E) × Fin (Module.finrank L E) → L := fun t =>
    Algebra.leftMulMatrix (Module.finBasis L E)
      (e (ratio (Ω := Ω c) (d.w t.1 c) (d.w (d.jc c) c))) t.2.1 t.2.2
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hne : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
      (∏ s ∈ Finset.univ.erase t, Q (mm s)) ≠ 0 := by
    intro t
    rw [map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  have hfrac : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (Q (mm t)) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t) * ∏ s ∈ Finset.univ.erase t, Q (mm s)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ s, Q (mm s)) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => Q (mm s)) (Finset.mem_univ t), map_mul, map_mul,
      mul_div_mul_right _ _ (hne t)]
  have hLtoC : ∀ l : L, algebraMap L (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) l =
      algebraMap (MvPolynomial (Fin (d.N + 1)) L) (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
        (MvPolynomial.C l) := by
    intro l
    rw [IsScalarTower.algebraMap_apply L (MvPolynomial (Fin (d.N + 1)) L)
      (FractionRing (MvPolynomial (Fin (d.N + 1)) L)), MvPolynomial.algebraMap_eq]
  refine ⟨Module.finrank L E, B, ∏ s, Q (mm s),
    fun j => Matrix.of fun a a' => P (mm (j, a, a')) * ∏ s ∈ Finset.univ.erase (j, a, a'), Q (mm s),
    ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  · intro x
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j a a' x
    simp only [Matrix.of_apply]
    rw [map_mul, map_prod, hPinv]
    congr 1
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j
    ext a a'
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [htr, he, hb'2, Matrix.map_apply, hLtoC, hPQ]
    exact hfrac (j, a, a')

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAF
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem b_mem (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (k : Fin d.del) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.PlOver la c) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := (d.admissible_over_prime hd h la c w hw).1
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem b_linIndep (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    LinearIndependent (KTf K d.D d.N) (d.bvecG hd.sel hd.a4.choose) := by
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  classical
  obtain ⟨-, hind, -⟩ := hd.a4.choose_spec
  rw [Fintype.linearIndependent_iff]
  intro q hq
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (KTp K d.D d.N)) Finset.univ q
  choose p hp using fun k => hint k (Finset.mem_univ k)
  have hsH : ∀ c (x : KTp K d.D d.N),
      d.sH c x = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := by
    intro c x
    rw [Data.KTtoS, IsFractionRing.lift_algebraMap]
    rfl
  have hzero : ∀ k, p k = 0 := hind p (fun c => by
    have hc := congrFun hq c
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hc
    simp only [Algebra.smul_def] at hc
    calc ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))
        = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s) *
            ∑ k, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N) (q k) *
              d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsH, hp k, Algebra.smul_def, map_mul, mul_assoc]
          rfl
      _ = 0 := by rw [hc, mul_zero])
  intro k
  have hk := hp k
  rw [hzero k, map_zero, Algebra.smul_def] at hk
  exact (mul_eq_zero.mp hk.symm).resolve_left
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)

theorem del_eq (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    d.del = ∑ c, Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
  Finset.sum_congr rfl fun c _ => (d.omS_finite hd h c).2.symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem norm_at_la (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2)
    (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0) :
    ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u :=
  d.norm_at_la_A hd h c la ϖ hϖ hϖ2 y hy


open MeasureTheory in
theorem norm_at_sg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) :=
  d.norm_at_sg_B hd h c sg

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Imports
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem exists_generic (hd : d.AxH 𝒜) (h : d.S1) :
    (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :=
  HtGenericPt 𝒜 d hd h

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceFib
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem trace_fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) (g : Ω c) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    tauPev sg _ hpt (Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
        (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)) =
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrk⟩ := d.omS_finite hd h c
  have : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (R := K) (algebraMap K (KTf K d.D d.N)).injective
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := fun i h0 => by
    have := hpt (X (i.succ, 0)) (X_ne_zero _)
    rw [eval₂_X, NPB.gpt_succ, h0, zero_mul] at this
    exact this rfl
  obtain ⟨hinj, hrange⟩ := d.fibre_core hd h c sg _ hpt
  rw [d.ST_scale c sg t y hy] at hrange
  rw [← hrange, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  exact trace_eq_sum_embeddings ℂ

theorem de_fibre (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      d.evT sg 0 (d.tOf z) b ≠ 0 →
      d.evT sg 0 (d.tOf z) a / d.evT sg 0 (d.tOf z) b =
        (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))).det := by
  haveI : Countable K := countable_numberField K
  filter_upwards [NPB.ae_gen (D := d.D) (N := d.N) sg] with z hz hb
  refine (div_eq_iff hb).2 ?_
  have hG : ∀ (m : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m p → p ≠ 0 →
      eval₂ sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) p ≠ 0 :=
    fun m p h1 h2 => hz m p h1 h2
  have h0 : ∀ q : MvPolynomial (TVar d.D d.N) K,
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2)
        (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) q =
        d.evT sg 0 (d.tOf z) q := by
    intro q
    unfold Data.evT
    congr 1
    funext v
    obtain ⟨i, j⟩ := v
    induction i using Fin.cases with
    | zero => simp [NPB.gpt]
    | succ i => simp [NPB.gpt]
  suffices H : ∀ Dv : ℂ, (∀ y : Fin (d.N + 1 + d.D) → ℂ,
      (∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
        eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) q ≠ 0) →
      eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) a =
        Dv * eval₂ sg (NPB.gpt (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) y) b) →
      d.evT sg 0 (d.tOf z) a = Dv * d.evT sg 0 (d.tOf z) b by
    refine H _ fun y hpt => ?_
    have h1 := congrArg (tauPev sg _ hpt) hab.2.1
    rw [map_mul, tauPev_apply, tauPev_apply] at h1
    rw [h1]
    congr 1
    rw [Data.De, RingHom.map_det]
    congr 1
    ext k l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have ht := d.trace_fib hd h c sg (d.tOf z) y hpt
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) *
        ratio (Ω := Ω c) (d.thp (hd.sel l) c) (hd.a4.choose c))
    simp only [map_mul] at ht
    simpa only [Data.bvecG] using ht
  intro Dv hDv
  have hR : NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) a -
      MvPolynomial.C Dv * NPB.psi sg (fun q : Fin d.D × Fin (d.N + 1) => d.tOf z q.1 q.2) b = 0 := by
    by_contra hR
    obtain ⟨y, hy, hgen⟩ := NPB.exists_gen sg _ hG _ hR
    apply hy
    rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, hDv y hgen, sub_self]
  have e0 := congrArg
    (MvPolynomial.eval (Fin.append (fun _ : Fin (d.N + 1) => (0 : ℂ)) (fun _ : Fin d.D => (1 : ℂ)))) hR
  rw [map_sub, map_mul, MvPolynomial.eval_C, NPB.eval_psi, NPB.eval_psi, h0, h0, map_zero] at e0
  exact sub_eq_zero.mp e0

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

