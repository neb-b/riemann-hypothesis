module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SupBoundCount

noncomputable section

theorem BlockResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    BlockResolutionFormsIndependent.Statement := by
  intro D K _ _ ι _ Ω _ _ d n r b hb a ha
  choose f hf hbf using hb.1
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg

  set F : ((Σ k, ι k) → ℂ) → ℂ := fun z => ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) with hF
  have ha' : ∀ x : d.R.X, F (blockPt d x) = 0 := by
    intro x
    have := ha x
    simp only [hbf, eval_map_int_rat] at this
    exact this
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb.2.1
    simp only [hbf, GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.aeval_map_int] at this
    exact this
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)

  have hev : ∀ (s : MRing ι) (e : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s e → ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
        (∏ k, c k ^ e k) * eval z (map (Int.castRingHom ℂ) s) := by
    intro s e hs c z
    rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : (∏ i : (Σ k, ι k), c i.1 ^ m i) = ∏ k, c k ^ e k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
    simp only [mul_pow, Finset.prod_mul_distrib, hc]
    ring

  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      F (fun p => c p.1 * z p) = (∏ k, c k ^ blockDeg d.k₀ n k) * F z := by
    intro c z
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev (f k) _ (hf k) c z]
    ring

  have hoff : ∀ z, z ∈ mcPts (mCoordIdeal d.y) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨x, c, hc, hxz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 := ha' x
    rw [show blockPt d x = d.R.lift x x from rfl, hxz, hsmul] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))

  have hpts : ∀ z ∈ mcPts (mCoordIdeal d.y), F z = 0 := by
    intro z hz
    have hcl := hND K ι (mCoordIdeal d.y) (D + 1) g d.arith hgP hz
    have hsub : {z | z ∈ mcPts (mCoordIdeal d.y) ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z | F z = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 hsub hcl
  exact coeff_eq_zero hli (mcPts_nonempty d) hpts

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartPrimePowerInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem aeval_mul_blockScale_of_isMultiHomog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [CommRing Ω] {f : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (t : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => y p * t p.1) f = aeval y f * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ x, t k ^ d ⟨k, x⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal {K : Type*} [Fintype K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω] {y : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) (t : K → Ω) : aeval (fun p => y p * t p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1) :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  rw [← hcomp, AlgHom.comp_apply, h0, map_zero]

theorem ChartPrimePowerInverse.proof : ChartPrimePowerInverse.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L hhom hL p hp j hj
  obtain ⟨N, hN⟩ := PullConeNull.proof K ι Ω y D L hL
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ,
      (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro c hc
    set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R := fun n => R.pow_mem (natCast_mem R p) n

    let G : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R}
        mul_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z) := by ring
          rw [this]
          exact R.mul_mem ha hb
        add_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z) := by
            ring
          rw [this]
          exact R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)
        algebraMap_mem' := by
          intro q
          obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'
          refine ⟨b, ?_⟩
          have hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω) := by exact_mod_cast hden
          have hd0 : (d' : Ω) ≠ 0 := by
            intro h0
            have : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            rw [hden', h0, mul_zero] at this
            exact this rfl
          have : (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹ := by
            rw [eq_ratCast, Rat.cast_def, hden']
            field_simp
          show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R
          rw [this]
          exact R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }
    have hmemG : ∀ x ∈ R, x ∈ G := fun x hx => ⟨0, by simpa using hx⟩
    let r : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, c q.1⟩
    let χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval r
    let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
    have hχG : ∀ g, χ g ∈ G := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C q => simpa [χ] using G.algebraMap_mem q
      | add f g hf hg => simpa using G.add_mem hf hg
      | mul_X f q hf =>
        simpa [χ] using G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))
    have hχmap : ∀ f : MRing ι,
        χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f := by
      intro f
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      simp only [r, t, div_eq_mul_inv]

    let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
      { carrier := {f | χ f * (Y / aeval y (L j)) ∈ G}
        add_mem' := by
          intro f g hf hg
          simpa [add_mul] using G.add_mem hf hg
        zero_mem' := by simp
        smul_mem' := by
          intro g f hf
          simpa [smul_eq_mul, mul_assoc] using G.mul_mem (hχG g) hf }
    have hIJ : coneNullIdeal y L ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]
        exact G.zero_mem
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]
        have : aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) =
            aeval y (L i) / aeval y (L j) := by
          have hprod : (∏ k, t k ^ e k) = Y⁻¹ := by
            rw [hYdef, ← Finset.prod_inv_distrib]
            exact Finset.prod_congr rfl fun k _ => inv_pow _ _
          rw [hprod]
          field_simp
        rw [this]
        exact hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))
    have h1 := hIJ (hN c)
    have hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1 := by
      simp [χ, r, div_self (hc _)]
    obtain ⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by
      have : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G := h1
      rwa [hone, one_mul] at this
    exact ⟨a, by rw [mul_div_assoc]; exact ha⟩
  choose! a ha using key
  refine ⟨Finset.univ.sup a, fun c hc => ?_⟩
  have hle : a c ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ c)
  have e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) =
      (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j)) := by
    rw [← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]
    ring
  rw [e1]
  exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtGenUniform
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter.AvoidRing (isMultiHomog_mul isMultiHomog_pow)

noncomputable section

namespace ClosedPtGenUniform

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem genNear_of_mul_eq_pow {d : K → ℤ} {a q b : MRingOver S ι} {α β δ : K → ℕ} {m : ℕ}
    (h : GenNear S ι 𝓜 d a α) (hq : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q β) (hab : a * q = b ^ m) (hdeg : m • δ = α + β) :
    GenNear S ι 𝓜 d b δ := by
  intro I x hx
  obtain ⟨n, t, c, r, p, z, ht, htc, hp, hz, he⟩ := h I x hx
  refine ⟨m * n, t, c, r, fun j => q ^ n * p j, z, ht, htc, fun j => ?_, hz, ?_⟩
  · have h' := GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hq n) (hp j)
    convert h' using 1
    funext k
    have hk := congrFun hdeg k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [mul_comm m n, mul_assoc, hk]
    ring
  · rw [pow_mul, ← hab, mul_pow, show a ^ n * q ^ n * t = q ^ n * (a ^ n * t) by ring, mul_smul, he,
      Finset.smul_sum]
    simp_rw [mul_smul]

theorem genNear_mul_pow (hM : GenNearMul.Statement) (hgr : KH.IsMGraded S ι 𝓜) {W : Ideal (MRingOver S ι)}
    (hW : W ≤ Module.annihilator (MRingOver S ι) M) {d n : K → ℤ} {f g : MRingOver S ι} {δ γ : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ) (hfd : GenNear S ι 𝓜 d f δ)
    (hgn : GenNear S ι (KH.quotPart S W) n g γ) :
    ∀ a : ℕ, GenNear S ι 𝓜 (d + a • n) (f * g ^ a) (δ + a • γ) := by
  intro a
  induction a with
  | zero => simpa using hfd
  | succ a ih =>
    have h' := hM S K ι M 𝓜 W (d + a • n) n (f * g ^ a) g (δ + a • γ) γ hgr hW
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hf (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hg a)) hg ih hgn
    rw [succ_nsmul, succ_nsmul, pow_succ, ← mul_assoc, ← add_assoc, ← add_assoc]
    exact h'

end ClosedPtGenUniform


open ClosedPtGenUniform in
theorem ClosedPtGenUniform.proof (hG : GradedSubmodules.Statement) (hF : ClosedPtFibreLift.Statement)
    (hN : ChartNakayamaGen.Statement) (hM : GenNearMul.Statement) : ClosedPtGenUniform.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e P hP
  classical
  obtain ⟨hPprime, hPhom, hPrel⟩ := hP.1
  choose i hi using hPrel

  let I : KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hI : ∀ k, ∀ j ∈ I.1 k, (X ⟨k, j⟩ : MRingOver S ι) ∉ P := by
    intro k j hj
    rw [Finset.mem_singleton.mp hj]
    exact hi k
  have : IsNoetherianRing (MRingOver S ι) := inferInstance

  obtain ⟨hWhom, hMsub⟩ := hG S K ι M 𝓜 hgr
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVPM : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) M) :=
    hV.trans (LinearMap.annihilator_le_of_injective (P • ⊤ : Submodule (MRingOver S ι) M).subtype
      (P • ⊤ : Submodule (MRingOver S ι) M).injective_subtype)
  obtain ⟨cM, hcM⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) M) (subGrading 𝓜 (P • ⊤)) inferInstance
    (hMsub P hPhom).1 hVPM e
  obtain ⟨fM, δM, hfM, hfMP, hgenM⟩ := hN S K ι M 𝓜 P (e + cM • N) hS hfin hgr hPprime hPhom I hI
    (hF S K ι M 𝓜 P (e + cM • N) hS hfin hgr hP (hcM cM le_rfl) I hI)

  set W := Module.annihilator (MRingOver S ι) M with hWdef
  have hWgr : KH.IsMGraded S ι (KH.quotPart S W) := QuotPartGraded.proof S K ι W hWhom
  have hQfin : Module.Finite (MRingOver S ι) (MRingOver S ι ⧸ W) := inferInstance
  obtain ⟨-, hQsub⟩ := hG S K ι (MRingOver S ι ⧸ W) (KH.quotPart S W) hWgr
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ W) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVQ : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ W) := by
    rw [Ideal.annihilator_quotient]
    exact hV
  have hVPQ : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)) :=
    hVQ.trans (LinearMap.annihilator_le_of_injective
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).subtype
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).injective_subtype)
  obtain ⟨cO, hcO⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W))
    (subGrading (KH.quotPart S W) (P • ⊤)) inferInstance (hQsub P hPhom).1 hVPQ 0
  have hgenO : ∀ n : ℕ, cO ≤ n → ∃ (g : MRingOver S ι) (γ : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ ∧ g ∉ P ∧
      GenNear S ι (KH.quotPart S W) (0 + n • N) g γ := fun n hn =>
    hN S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hPprime hPhom I hI
      (hF S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hP (hcO n hn) I hI)
  set n₁ := cO + 1 with hn₁
  obtain ⟨g₁, γ₁, hg₁, hg₁P, hgen₁⟩ := hgenO n₁ (by omega)
  obtain ⟨g₂, γ₂, hg₂, hg₂P, hgen₂⟩ := hgenO (n₁ + 1) (by omega)

  refine ⟨fM * g₁ * g₂, δM + γ₁ + γ₂, cM + n₁ * n₁, GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hfM hg₁) hg₂, ?_, ?_⟩
  · intro hmem
    rcases hPprime.mem_or_mem hmem with h | h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hfMP h
      · exact hg₁P h
    · exact hg₂P h
  intro c hc
  have hpos : 0 < n₁ := by omega
  set q := (c - cM) / n₁ with hq
  set s := (c - cM) % n₁ with hs
  have hdm : n₁ * q + s = c - cM := Nat.div_add_mod (c - cM) n₁
  have hsn : s < n₁ := Nat.mod_lt _ hpos
  have hqn : n₁ ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hpos]
    omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_trans hsn.le hqn)
  have hca : c = cM + a * n₁ + s * (n₁ + 1) := by
    have h1 : c - cM + cM = c := Nat.sub_add_cancel (by omega)
    rw [← h1, ← hdm, ha]
    ring
  have hA := genNear_mul_pow hM hgr le_rfl hfM hg₁ hgenM hgen₁ a
  have hB := genNear_mul_pow hM hgr le_rfl (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hfM (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hg₁ a)) hg₂ hA hgen₂ s
  have htw : e + cM • N + a • (0 + n₁ • N) + s • (0 + (n₁ + 1) • N) = e + c • N := by
    rw [hca]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    push_cast
    ring
  rw [htw] at hB
  refine genNear_of_mul_eq_pow hB
    (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hfM (a + s)) (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hg₁ (s + 1)))
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow hg₂ (a + 1))) (m := a + s + 1) (by ring) ?_
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFSGeomDegPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem FSGeomDegPos.proof (hDeg : DegreeStatement) (hPos : MultiDegreePositive.Statement) :
    FSGeomDegPos.Statement := by
  intro K _ ι _ P e hP
  classical
  have hS : ∀ j : Fin e, IsSmoothHerm ((fun _ : Fin e => fsH ι) j) := fun _ =>
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have ha : (fun j : Fin e => ((fun _ : Fin e => fsH ι) j).a) = fun _ : Fin e => fun _ : K => (1 : ℤ) := by
    funext j k
    simp [fsH, HermLine.ofMetrics]
  obtain ⟨hq, hd⟩ := ZCombLimit.genericFibre hP
  have hpos := hPos ℚ K ι _ e hq hd
  rw [GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e _ 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at hpos
  rw [hDeg K ι P e (fun _ => fsH ι) 2 hP hS Nat.prime_two, ha,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  exact_mod_cast hpos

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem aeval_map_intRat_eq {σ : Type} (x : σ → ℂ) (f : MvPolynomial σ ℤ) :
    aeval x (map (algebraMap ℤ ℚ) f) = eval x (map (Int.castRingHom ℂ) f) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem FibreNormBadPrimesFinite.proof : FibreNormBadPrimesFinite.Statement := by
  intro K _ ι _ Ω _ _ y D e L _ _ _ _ hC
  set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef
  have key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧
      ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I := by
    intro c
    set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩
    set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I
    have hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0 := fun g hg => by
        rw [← aeval_map_intRat_eq, ← algebraMap_def]
        exact hx _ (Ideal.mem_map_of_mem _ hg)
      rw [algebraMap_def, aeval_map_intRat_eq]
      by_contra hne
      simp only [f, map_prod, map_X, eval_X] at hne
      have hblk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)
      obtain ⟨j, hj⟩ := hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩
      exact hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    rw [vanishingIdeal_zeroLocus_eq_radical] at hv
    obtain ⟨r, hr⟩ := hv
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]
      at hr
    obtain ⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩ := hr
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.1 hm
    refine ⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩
    have hinj : Function.Injective (map (σ := Σ k, ι k) (algebraMap ℤ ℚ)) :=
      map_injective _ (algebraMap ℤ ℚ).injective_int
    have hu' : f ^ r * C n = u := hinj (by simpa only [algebraMap_def, map_mul] using h)
    rw [mul_comm, hu']
    exact hu
  choose N hN r hr using key
  refine Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_
  rintro p ⟨hp, hH⟩
  obtain ⟨z, hz, hP, hL⟩ := hH
  choose c hc using hz
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))) :=
    sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))
  have h1 := hker (hr c)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast,
    map_intCast] at h1
  have hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)
  have hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0 := (mul_eq_zero.1 h1).resolve_right hprod
  rw [CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at hNz
  simp only [Set.mem_iUnion, Set.mem_Iic]
  exact ⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

