module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscreteValuationPoint

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

def HtOne : Set (Ideal (KTp K d.D d.N)) := {p | p.IsPrime ∧ p.height = 1}

noncomputable def gen (p : Ideal (KTp K d.D d.N)) : KTp K d.D d.N :=
  open Classical in if hp : p.IsPrincipal then (haveI := hp; Submodule.IsPrincipal.generator p) else 0

noncomputable def dg (q : KTp K d.D d.N) : ℕ := q.support.sup fun s => ∑ j, s (1, j)

def OverP (c : ι) (p : Ideal (KTp K d.D d.N)) : Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : KTp K d.D d.N, 0 ≤ w (d.sH c x) ∧ (0 < w (d.sH c x) ↔ x ∈ p)}

def GoodP (c : ι) (p : Ideal (KTp K d.D d.N)) : Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | w ∈ d.OverP c p ∧ ∃ a : Ω c, a ≠ 0 ∧ d.Wres c w a ≠ 0}

noncomputable def nP (h : d.S1) (c : ι) (G : WT) (ta : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.ord c (d.Wres c w) G ta

noncomputable def ordMM (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (f : A c) : ℤ :=
  d.ord c v d.wL f - ⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)

noncomputable def nPMM (h : d.S1) (c : ι) (f : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) f

noncomputable def aG (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℤ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)

noncomputable def h0f (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℝ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    (d.nP h c G (ta c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)

noncomputable def NlaG (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ord c (d.Wres c w) G (ta c) : ℝ)

noncomputable def Nsg (G : WT) (ta : ∀ c, A c) (sg : K →+* ℂ) : ℝ :=
  ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c G (ta c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

noncomputable def Hgt (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) + meanK (d.Nsg G ta) +
    d.h0f h G ta

noncomputable def NlaMM (h : d.S1) (f : ∀ c, A c) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)

noncomputable def NsgMM (f : ∀ c, A c) (sg : K →+* ℂ) : ℝ :=
  ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

noncomputable def mahlerMeasureHeight (h : d.S1) (f : ∀ c, A c) : ℝ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)

noncomputable def HgtMM (h : d.S1) (f : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.NlaMM h f la * logNorm la) / (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM f) +
    d.mahlerMeasureHeight h f

noncomputable def wx (x : Fin (d.N + 1) → K) : ∀ c, A c := ∑ j, x j • d.w j

noncomputable def rationalBaseRow (c : ι) : OmS (Ω c) d.D d.N :=
  ∑ j, d.sH c (MvPolynomial.X (0, j)) *
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))

noncomputable def fZ (h : d.S1) (c : ι) : KTf K d.D d.N :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulVecSmul
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder

section Real

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

abbrev hIdx (K : Type) [Field K] [NumberField K] (r : ℕ) : Type := (K →+* ℂ) × Fin r × Fin 2

noncomputable def hReF (x : (K →+* ℂ) → Fin r → ℂ) : hIdx K r → ℝ :=
  fun p => if p.2.2 = 0 then (x p.1 p.2.1).re else (x p.1 p.2.1).im

noncomputable def hRe (x : (K →+* ℂ) → Fin r → ℂ) : EuclideanSpace ℝ (hIdx K r) :=
  WithLp.toLp 2 (hReF x)

theorem realCoordsFun_add (x y : (K →+* ℂ) → Fin r → ℂ) : hReF (x + y) = hReF x + hReF y := by
  funext p
  simp only [hReF, Pi.add_apply]
  split_ifs <;> simp

theorem inner_hRe (x y : (K →+* ℂ) → Fin r → ℂ) :
    inner ℝ (hRe x) (hRe y) = (∑ σ, star (x σ) ⬝ᵥ y σ).re := by
  simp only [hRe, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, dotProduct, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hReF]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
  simp
  ring

theorem star_dotProduct_self_re {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = hns v := by
  simp only [dotProduct, Complex.re_sum, hns, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_realCoords_sq (x : (K →+* ℂ) → Fin r → ℂ) : ‖hRe x‖ ^ 2 = ∑ σ, hns (x σ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]
  exact Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _

noncomputable def hpv (b : Fin k → Fin r → K) (q : Fin r → K) : EuclideanSpace ℝ (hIdx K r) :=
  hRe fun σ => hPm σ b *ᵥ fun l => σ (q l)

theorem projectedVector_add (b : Fin k → Fin r → K) (q q' : Fin r → K) :
    hpv b (q + q') = hpv b q + hpv b q' := by
  have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((q + q') l)) =
      (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) +
        (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q' l)) := by
    funext σ
    rw [Pi.add_apply, ← mulVec_add]
    congr 1
    funext l
    simp [map_add]
  simp only [hpv, hRe, e, realCoordsFun_add, WithLp.toLp_add]

theorem projectedVector_zero (b : Fin k → Fin r → K) : hpv b 0 = 0 := by
  have e : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((0 : Fin r → K) l)) = 0 := by
    funext p
    simp only [hReF, Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, mulVec_zero]
    split_ifs <;> simp
  simp only [hpv, hRe, e, WithLp.toLp_zero]

noncomputable def hpvHom (b : Fin k → Fin r → K) : (Fin r → K) →+ EuclideanSpace ℝ (hIdx K r) where
  toFun := hpv b
  map_zero' := projectedVector_zero b
  map_add' := projectedVector_add b

theorem normSqSum_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < hns v := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hv
  have h1 : 0 < ‖v l‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hl) 2
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l))

theorem projectedVector_eq_zero_iff {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hpv b q = 0 ↔ q ∈ Submodule.span K (Set.range b) := by
  constructor
  · intro h0
    by_contra hq
    have hpos : Fintype.card (K →+* ℂ) ≠ 0 := by
      rw [NumberField.Embeddings.card K ℂ]; exact Module.finrank_pos.ne'
    obtain ⟨σ0⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)
    have h1 := norm_realCoords_sq (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l))
    rw [← hpv, h0, norm_zero] at h1
    have h2 : 0 < ∑ σ, hns (hPm σ b *ᵥ fun l => σ (q l)) :=
      lt_of_lt_of_le (normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ0 hb hq))
        (Finset.single_le_sum (f := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ σ0))
    rw [← h1] at h2
    norm_num at h2
  · intro hq
    have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      funext σ
      exact orthogonalProjector_mulVec_eq_zero σ hb hq
    have e2 : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      rw [e]; funext p; simp [hReF]
    simp only [hpv, hRe, e2, WithLp.toLp_zero]

theorem orthogonalProjector_mulVec_smul (σ : K →+* ℂ) (b : Fin k → Fin r → K) (a : K) (x : Fin r → K) :
    (hPm σ b *ᵥ fun l => σ ((a • x) l)) = σ a • (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [← mulVec_smul]
  congr 1
  funext l
  simp [map_smul]

theorem inner_projectedVector_smul (b : Fin k → Fin r → K) (a a' : K) (x y : Fin r → K) :
    inner ℝ (hpv b (a • x)) (hpv b (a' • y)) =
      (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))).re := by
  rw [hpv, hpv, inner_hRe]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def]
  ring

end Real

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegAVpt
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem av_point {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 :=
  DiscreteValuationPoint.exists_dvr_point_flat_algebra hsp e he

end ReciprocityTheory.ChartRestriction.G.T0
end

