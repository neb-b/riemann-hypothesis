module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGraphDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameGraphDeg.proof
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPt : ProjFrameFibrePt.Statement) (hDeg : ProjFrameFibreDeg.Statement) : ProjFrameGraphDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF
  have : (coordIdeal ℤ x).IsPrime := hP.2.1.1
  have := ProjFrameGraph.graphIdeal_isPrime (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
    (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
  let G := Inter.genFibreOf (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
    (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e)))
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr)
  have hch := ProjFrameGraph.isChart_fibreChart G (e 0).2 (ProjFrameGraph.frame_ne_zero hF 0)
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ (hPt D Ω κ x e hP hF G) hch, hDeg D Ω κ x e hP hF G _ hch]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNullModP
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem exists_natMul_mem_of_map_rat_mem {σ : Type} (I : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ)
    (hf : map (Int.castRingHom ℚ) f ∈ Ideal.map (map (Int.castRingHom ℚ)) I) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : MvPolynomial σ ℤ) * f ∈ I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
  have hA : (map (Int.castRingHom ℚ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ) =
      algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) := by
    rw [algebraMap_def, algebraMap_int_eq]
  rw [hA, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := σ)))] at hf
  obtain ⟨⟨⟨g, hg⟩, ⟨_, m, hm, rfl⟩⟩, h⟩ := hf
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)) := by
    rw [← hA]; exact map_injective _ Int.cast_injective
  have h' : C m * f = g := by rw [mul_comm]; exact hinj (by simpa using h)
  obtain ⟨t, ht⟩ : m ∣ (m.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.ne_zero hm), ?_⟩
  have : (m.natAbs : MvPolynomial σ ℤ) = C (m.natAbs : ℤ) := (map_natCast C _).symm
  rw [this, ht, C_mul, mul_comm (C m), mul_assoc, h']
  exact I.mul_mem_left _ hg

theorem PullConeNullModP.proof : PullConeNullModP.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL p hp hbad
  have : Fact p.Prime := ⟨hp⟩
  have hQ : coneNullIdeal y L = (coneNullIdealZ y L).map (map (Int.castRingHom ℚ)) := by
    rw [coneNullIdeal, coneNullIdealZ, Ideal.map_span, Set.image_union, ← Set.range_comp]; rfl
  set I := coneNullIdealZ y L
  let π := Ideal.Quotient.mk I
  obtain ⟨N₁, hN₁⟩ := PullConeNull.proof K ι Ω y D L hL

  have key : ∀ c : ∀ k, ι k, ∃ N M : ℕ, ¬ p ∣ M ∧
      (M : MRing ι ⧸ I) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N = 0 := by
    intro c
    set u := π (∏ k, (X ⟨k, c k⟩ : MRing ι))

    obtain ⟨M₁, hM₁, h₁⟩ := exists_natMul_mem_of_map_rat_mem I ((∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N₁)
      (by rw [← hQ]; simpa [map_prod] using hN₁ c)
    have e₁ : (M₁ : MRing ι ⧸ I) * u ^ N₁ = 0 := by
      rw [← map_natCast π, ← map_pow, ← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁

    obtain ⟨N₂, h, e₂⟩ : ∃ N₂ h, u ^ N₂ = (p : MRing ι ⧸ I) * h := by
      let φ : MRing ι →+* MvPolynomial (Σ k, ι k) (ZMod p) := map (Int.castRingHom (ZMod p))
      have hrad : φ (∏ k, (X ⟨k, c k⟩ : MRing ι)) ∈ (I.map φ).radical := by
        rw [← IsJacobsonRing.out inferInstance (Ideal.radical_isRadical (I.map φ)), Ideal.jacobson, Submodule.mem_sInf]
        rintro m ⟨hJm, hm⟩
        letI := Ideal.Quotient.field m
        have := finite_of_finite_type_of_isJacobsonRing (ZMod p) (MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let ψ := IsAlgClosed.lift (R := ZMod p) (M := AlgebraicClosure (ZMod p))
          (S := MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let z : (Σ k, ι k) → AlgebraicClosure (ZMod p) := fun q => ψ (Ideal.Quotient.mk m (X q))
        have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) =
            ψ (Ideal.Quotient.mk m (φ f)) := by
          intro f
          have e : (eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))) =
              ((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ := by
            refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
            · exact RingHom.congr_fun (RingHom.ext_int
                (((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))).comp C)
                ((((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ).comp C)) r
            · simp [z, φ]
          exact RingHom.congr_fun e f
        have hker : ∀ f : MRing ι, f ∈ I → ψ (Ideal.Quotient.mk m (φ f)) = 0 := fun f hf => by
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.le_radical (Ideal.mem_map_of_mem φ hf))), map_zero]
        by_contra hc
        refine hbad ⟨z, fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_, fun j => ?_⟩
        · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
          refine Ideal.mul_mem_right _ m (Ideal.Quotient.eq_zero_iff_mem.mp (ψ.injective ?_))
          simpa [z, φ] using h0
        · rw [hev]; exact hker f (Ideal.subset_span (Or.inl hf))
        · rw [hev]; exact hker _ (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
      rw [← map_pow, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective φ (map_surjective _ ZMod.intCast_surjective)] at hn
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hn
      have hb' : b ∈ RingHom.ker φ := by simpa [RingHom.mem_ker] using hb
      rw [ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at hb'
      obtain ⟨h, rfl⟩ := hb'
      refine ⟨n, π h, ?_⟩
      rw [← map_pow, ← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_natCast C p,
        map_natCast, mul_comm]

    obtain ⟨a, M₀, hM₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₁ p hp.ne_one
    refine ⟨a * N₂ + N₁, M₀, hM₀, ?_⟩
    rw [pow_add, pow_mul', e₂, mul_pow]
    push_cast at e₁
    linear_combination h ^ a * e₁
  choose Nc Mc hMc hc using key
  refine ⟨Finset.univ.sup Nc, ∏ c, Mc c, ?_, fun c => ?_⟩
  · exact fun hdvd => (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd |>.elim fun c ⟨_, h⟩ => hMc c h
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
      ← Nat.add_sub_cancel' (Finset.le_sup (f := Nc) (Finset.mem_univ c)), pow_add]
    push_cast
    linear_combination ((∏ c' ∈ Finset.univ.erase c, (Mc c' : MRing ι ⧸ I)) *
      π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ (Finset.univ.sup Nc - Nc c)) * hc c

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatioFieldDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RatioFieldDeg

variable {ι : Type}

def quotCone {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ)) (hu : coordIdeal ℤ u = I) :
    MvPolynomial ι ℤ ⧸ I →+* Polynomial E :=
  Ideal.Quotient.lift I (coneMap ℤ u).toRingHom (fun a ha => by rw [← hu] at ha; exact ha)

theorem quotCone_injective {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : Function.Injective (quotCone u I hu) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, ← hu, coordIdeal, RingHom.mem_ker]
  simpa [quotCone] using ha

theorem isDomain_quot {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : IsDomain (MvPolynomial ι ℤ ⧸ I) :=
  Function.Injective.isDomain _ (quotCone_injective u I hu)

theorem charZero_frac {E : Type} [Field E] [CharZero E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) [IsDomain (MvPolynomial ι ℤ ⧸ I)] :
    CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I)) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  refine ⟨fun n m h => ?_⟩
  have h' := congrArg (IsFractionRing.lift hg) h
  simp only [map_natCast] at h'
  exact Nat.cast_injective h'

section

variable (I : Ideal (MvPolynomial ι ℤ)) [IsDomain (MvPolynomial ι ℤ ⧸ I)]

def coord (i : ι) : FractionRing (MvPolynomial ι ℤ ⧸ I) :=
  algebraMap _ _ (Ideal.Quotient.mk I (X i))

variable [CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I))]

def ratField {κ : Type} (s : κ → ι) : IntermediateField ℚ (FractionRing (MvPolynomial ι ℤ ⧸ I)) :=
  IntermediateField.adjoin ℚ {t | ∃ k l, t = coord I (s k) / coord I (s l)}

theorem projDeg_eq {E : Type} [Field E] [CharZero E] (u : ι → E) (hu : coordIdeal ℤ u = I) {D : ℕ}
    (e : Fin (D + 1) → ι) :
    projDeg u e = IntermediateField.relfinrank (ratField I e) (ratField I id) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  let f : FractionRing (MvPolynomial ι ℤ ⧸ I) →ₐ[ℚ] RatFunc E := (IsFractionRing.lift hg).toRatAlgHom
  let c : E →ₐ[ℚ] RatFunc E := (RatFunc.C : E →+* RatFunc E).toRatAlgHom
  have hx : ∀ i, f (coord I i) = RatFunc.C (u i) * RatFunc.X := by
    intro i
    simp [f, coord, IsFractionRing.lift_algebraMap, quotCone, coneMap, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
  have hr : ∀ i j, f (coord I i / coord I j) = c (u i / u j) := by
    intro i j
    rw [map_div₀, hx, hx, mul_div_mul_right _ _ RatFunc.X_ne_zero]
    simp [c, map_div₀]
  have hmap : ∀ {κ : Type} (s : κ → ι), (ratField I s).map f = (fnField (u ∘ s)).map c := by
    intro κ s
    rw [ratField, fnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, (hr _ _).symm⟩
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, hr _ _⟩
  rw [← IntermediateField.relfinrank_map_map (ratField I e) (ratField I id) f, hmap, hmap,
    IntermediateField.relfinrank_map_map]
  rfl

end

theorem proof : RatioFieldDeg.Statement := by
  intro ι E₁ E₂ _ _ _ _ u v D e h
  have : IsDomain (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u) := isDomain_quot u _ rfl
  have : CharZero (FractionRing (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u)) := charZero_frac u _ rfl
  rw [projDeg_eq (coordIdeal ℤ u) u rfl e, projDeg_eq (coordIdeal ℤ u) v h.symm e]

end RatioFieldDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem ResolutionMixedBridge.proof : ResolutionMixedBridge.Statement := by
  intro D Ω _ _ κ _ d M m₁ hM hm₁
  have hex : ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (coordIdeal ℤ d.x) Ψ :=
    goodProjExists Unit (GlobalTheory κ) (coordIdeal ℤ d.x) D d.arith
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory κ) := (HermLine.ofCone m₁).tensor (HermLine.ofCone d.m).inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, HermLine.ofCone]
  have hgl : logRatio d.m m₁ = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, HermLine.ofCone, logRatio, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor (gbamix_smoothHerm_ofCone hm₁)
      (isSmoothHerm_inv (gbamix_smoothHerm_ofCone d.smooth)))
  have hsec : IsSectionOn (coordIdeal ℤ d.x) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose (fun j => HermLine.ofCone (M j)) B.inv 1 d.arith
    hex.choose_spec (fun j => gbamix_smoothHerm_ofCone (hM j)) hBs hsec
  unfold ptsIntegral
  rw [dite_eq_left hex, hgl]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiposTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTranscRatioDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem TranscRatioDeg.proof : TranscRatioDeg.Statement := by
  intro ι E _ _ u D e w i₀ Φ _ _ hi₀ he hw ht hΦ
  have ht0 : w 0 ≠ 0 := by
    intro h0
    apply ht
    rw [h0]
    exact isAlgebraic_zero
  have hwk : ∀ k, w k = w 0 * (u (e k) / u (e 0)) := fun k => by
    rw [mul_div_assoc', ← hw k, mul_div_cancel_right₀ _ (he 0)]

  have hfn : ∀ {κ : Type} (v : κ → E) (K : Subfield E), (∀ i j, v i / v j ∈ K) →
      ∀ x ∈ fnField v, x ∈ K := by
    intro κ v K hK x hx
    have : (fnField v).toSubfield ≤ K := by
      unfold fnField
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨q, rfl⟩ | ⟨i, j, rfl⟩)
      · rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem K q
      · exact hK i j
    exact this hx
  have hrat : ∀ i j, u i / u j ∈ fnField u := fun i j =>
    IntermediateField.subset_adjoin ℚ _ ⟨i, j, rfl⟩
  have hle : fnField (u ∘ e) ≤ fnField u := fun x hx =>
    hfn (u ∘ e) (fnField u).toSubfield (fun k l => hrat (e k) (e l)) x hx
  set F₀ := fnField (u ∘ e)
  set A := IntermediateField.extendScalars hle
  set L := IntermediateField.adjoin F₀ {w 0}

  have hL : ∀ x, x ∈ L ↔ x ∈ Subfield.closure (Set.range w) := by
    have h1 : L.toSubfield ≤ Subfield.closure (Set.range w) := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | h)
      · refine hfn (u ∘ e) _ (fun k l => ?_) x hx
        have : (u ∘ e) k / (u ∘ e) l = w k / w l := by
          rw [hwk k, hwk l]
          field_simp [ht0, he 0, he l]
          simp only [Function.comp_apply]
          ring
        rw [this]
        exact div_mem (Subfield.subset_closure ⟨k, rfl⟩) (Subfield.subset_closure ⟨l, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact Subfield.subset_closure ⟨0, rfl⟩
    have h2 : Subfield.closure (Set.range w) ≤ L.toSubfield := by
      rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      rw [hwk k]
      have hr : u (e k) / u (e 0) ∈ F₀ := IntermediateField.subset_adjoin ℚ _ ⟨k, 0, rfl⟩
      exact mul_mem (IntermediateField.mem_adjoin_simple_self F₀ (w 0))
        (IntermediateField.algebraMap_mem L (⟨_, hr⟩ : F₀))
    exact fun x => ⟨fun hx => h1 hx, fun hx => h2 hx⟩
  have hLset : Set.range (algebraMap L E) = (Subfield.closure (Set.range w) : Set E) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hL _).1 y.2
    · intro hx
      exact ⟨⟨x, (hL x).2 hx⟩, rfl⟩

  have hQ : ∀ x ∈ fnField u, x ∈ Subfield.closure (Set.range u) := hfn u _ fun i j =>
    div_mem (Subfield.subset_closure ⟨i, rfl⟩) (Subfield.subset_closure ⟨j, rfl⟩)
  have htA : Transcendental A (w 0) :=
    TranscRatioDeg.transcendental_of_subfield (Subfield.closure (Set.range u)) (fun x => hQ _ x.2)
      (algebraMap A E).injective (TranscRatioDeg.transcendental_subfieldClosure u (w 0) ht)
  have key := TranscRatioDeg.finrank_adjoin_eq_of_transcendental A htA
  have hproj : projDeg u e = Module.finrank F₀ A := IntermediateField.relfinrank_eq_finrank_of_le hle
  rw [hproj, ← key]
  apply TranscRatioDeg.finrank_adjoin_congr
  · rw [hΦ]
    apply SetLike.ext'
    rw [RingHom.coe_fieldRange, hLset]
  · rw [← RingHom.coe_fieldRange, hΦ, hLset]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro _ (h | ⟨i, rfl⟩)
      · exact Subfield.subset_closure (Or.inl h)
      · exact Subfield.subset_closure (Or.inr (hrat i i₀))
    · rw [Subfield.closure_le]
      rintro x (h | h)
      · exact Subfield.subset_closure (Or.inl h)
      · refine hfn u _ (fun i j => ?_) x h
        have : u i / u j = (u i / u i₀) / (u j / u i₀) := by
          rw [div_div_div_cancel_right₀ hi₀]
        rw [this]
        exact div_mem (Subfield.subset_closure (Or.inr ⟨i, rfl⟩))
          (Subfield.subset_closure (Or.inr ⟨j, rfl⟩))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

