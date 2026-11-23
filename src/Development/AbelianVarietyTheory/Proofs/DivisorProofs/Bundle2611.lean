module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSectionRatioEqBasePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thick_apply_eq_closedPoint {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ)
    (p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :
    thick R (maximalIdeal R) e p = closedPoint R := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  apply PrimeSpectrum.ext
  show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal = maximalIdeal R
  have hle : maximalIdeal R ^ (e + 1) ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal := by
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have hm : maximalIdeal R ≤ Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) p.asIdeal :=
    (Ideal.IsPrime.comap _).le_of_pow_le hle
  exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap _).ne_top hm).symm

theorem exists_thick_zero {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ) (G : Over (Sp R))
    (y : (thickObj R (maximalIdeal R) e G).left) :
    ∃ y₀ : (thickObj R (maximalIdeal R) 0 G).left,
      (fstG (maximalIdeal R) 0 G).left y₀ = (fstG (maximalIdeal R) e G).left y := by
  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have h1 : G.hom (pullback.fst G.hom (thick R (maximalIdeal R) e) y) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, thick_apply_eq_closedPoint]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) 0)
    (pullback.fst G.hom (thick R (maximalIdeal R) e) y) (closedPoint _)
    (h1.trans (thick_apply_eq_closedPoint 0 _).symm)
  exact ⟨z, hz⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_secRatioEq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e k k' : ℕ), 3 ≤ k → ∀ (x : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U e k k' hk x T hT y s₀ i' hy
  obtain ⟨y₀, hy₀⟩ := exists_thick_zero e G (x.left y)
  obtain ⟨s₁, j, hs₁⟩ := _root_.GlobalTheory.Mum.ClosedFibreBpf.exists_sec_ne_zero_at R hB D A G hG U k hk y₀
  refine ⟨j, ?_⟩
  have hs₁' : (fstG (maximalIdeal R) 0 G).left y₀ ∈ G.left.basicOpen (s₁.f j) :=
    (Scheme.preimage_basicOpen (fstG (maximalIdeal R) 0 G).left (s₁.f j)).ge hs₁
  have hu : y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen
      (((x.left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L j)).hom (s₁.f j)) := by
    refine (Scheme.preimage_basicOpen (x.left ≫ (fstG (maximalIdeal R) e G).left) (s₁.f j)).le ?_
    show (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ G.left.basicOpen (s₁.f j)
    rw [Scheme.Hom.comp_apply, ← hy₀]
    exact hs₁'
  by_contra hn
  have hE := congrArg (thickObj R (maximalIdeal R) e G).left.basicOpen (hT s₁ s₀ j i')
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_res] at hE
  have hmem : y ∈ ((x.left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L j ⊓
      (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i') := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨Scheme.basicOpen_le _ _ hu, Scheme.basicOpen_le _ _ hy⟩
  have h2 := hE.le (by
    simp only [TopologicalSpace.Opens.mem_inf] at hmem ⊢
    exact ⟨⟨hmem, hu⟩, ⟨hmem, hy⟩⟩)
  simp only [TopologicalSpace.Opens.mem_inf] at h2
  exact hn h2.1.2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrobeniusKernelIdealOfZeroDifferential
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit (R := K) b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  have hadd {A : Type} [CommRing A] (h : (p : A) = 0) (x y : A) :
      (x + y) ^ p = x ^ p + y ^ p := by
    rw [add_pow_prime_eq (Fact.out : p.Prime), h]; simp
  have hcast (A : Type) [CommRing A] [Algebra K A] : (p : A) = 0 := by
    rw [← map_natCast (algebraMap K A), CharP.cast_eq_zero, map_zero]
  have hmk (x : H) : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) x ^ p =
      algebraMap K _ (counit (R := K) x) ^ p := by
    have hx : x - algebraMap K H (counit (R := K) x) ∈ augIdeal K H := by
      simp [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        ((x - algebraMap K H (counit (R := K) x)) ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
    have e : x = (x - algebraMap K H (counit (R := K) x)) + algebraMap K H (counit (R := K) x) := by ring
    conv_lhs => rw [e, ← map_pow, hadd (hcast H), map_add, h0, zero_add, map_pow, AlgHom.commutes]
  have hmap (t : H ⊗[K] H) :
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
        (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) t ^ p =
      (1 : H ⧸ frobKerIdeal p K H) ⊗ₜ[K] (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)
        (TensorProduct.lid K H (LinearMap.rTensor H (counit (R := K) (A := H)) t)) ^ p) := by
    induction t with
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [hadd (hcast _), hadd (hcast _), hx, hy, tmul_add]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, hmk,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, smul_pow, ← map_pow,
        Algebra.algebraMap_eq_smul_one, smul_tmul]
  haveI : (frobKerIdeal p K H).IsHopfIdeal K := {
    counit_eq_zero x hx := frobKerIdeal_le_augIdeal (Fact.out : p.Prime).ne_zero K H hx
    map_mkQ_comul_eq_zero x hx := by
      have h : frobKerIdeal p K H ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
            (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))).comp (comulAlgHom K H)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply, hmap,
          comulAlgHom_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul, ← map_pow]
        have : Ideal.Quotient.mkₐ K (frobKerIdeal p K H) (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [this, tmul_zero]
      exact h hx
    antipode_mem x hx := by
      have h : frobKerIdeal p K H ≤ (frobKerIdeal p K H).comap (HopfAlgebra.antipodeAlgHom K H) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := K) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx }
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit (R := K) (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem maDens_locPot_eq_dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun i y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      dens L c (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hH (i) : hessC (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      ((2⁻¹ : ℝ) : ℂ) • c.hess (L i).φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) := by
    have hd := (L i).cInf.contDiffAt c (c.finChart.map_target hz)
      (mem_pick (L i).φ.isLB (c.finChart.symm z))
    rw [hr] at hd
    have e : (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
        ((fun v => (L i).φ.φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
      funext fun _ => div_eq_inv_mul _ _
    rw [e, hessC_const_mul', AlgChart.hess, hr, cHess_eq_hessC hd]
  have hτ (τ : Equiv.Perm (Fin D)) : (Matrix.of fun j l => (((2⁻¹ : ℝ) : ℂ) •
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z)) j l).det =
      (((2⁻¹ : ℝ) ^ D : ℝ) : ℂ) * (Matrix.of fun j l =>
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l).det := by
    refine (Matrix.det_smul (Matrix.of fun j l => c.hess (L (τ l)).φ
      (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l) ((2⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Fintype.card_fin, Complex.ofReal_pow]
  have hf : (1 / (D.factorial : ℂ)) = ((1 / (D.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h2 : (2 / Real.pi) ^ D * (2⁻¹ : ℝ) ^ D = (Real.pi ^ D)⁻¹ := by
    rw [← mul_pow, ← inv_pow]
    congr 1
    ring
  simp only [maDens, hH, ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, hτ, dens]
  rw [← Finset.mul_sum, hf, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h2]
  field_simp

variable {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_locPot_eq_dens (L : Fin D → MLine p σ) (hA : IsAlgAtlas A) (j : Fin A.n)
    {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target) : locDens A (fun i => (L i).φ.locPot) j z =
      dens L (hA.anRead.chart j) ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact maDens_locPot_eq_dens L _ hz

theorem part_eq_lintegral_locDens [SecondCountableTopology (CxPts p σ)] (L : Fin D → MLine p σ)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : part L ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun i => (L i).φ.locPot) j y) 0) := by
  have hl (y) := locDens_locPot_eq_dens L hA j (z := y)
  generalize locDens A (fun i => (L i).φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [_root_.GlobalTheory.Mix.part_apply k X p σ D L ε c S hS hs,
    ← measurePreserving_toV.setLIntegral_comp_preimage_emb (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

theorem int_eq_mInt (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ)
    (A : FinHolAtlas D (CxPts p σ)) (hA : IsAlgAtlas A) (L : Fin D → MLine p σ)
    (g : CxPts p σ → ℝ) (hg : Measurable g) :
    (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧
      (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun i => (L i).φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (L i).cInf).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (part_eq_lintegral_locDens L hA ε) hg (back hm ε)
  have fwd (hi : Intg L g) : MIntegrable A (fun i => (L i).φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (part_eq_lintegral_locDens L hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 hi.1.integrableOn) (key (-1) hi.2.integrableOn)).congr
      (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1, (pieces hm (-1)).1⟩⟩, fun hi => ?_⟩
  have hm := fwd hi
  have hmi : mInt A (fun i => (L i).φ.locPot) g = integralWith A hne.some (fun i => (L i).φ.locPot) g := by
    unfold mInt
    rw [dite_eq_left hne]
  rw [Mix.int, (pieces hm 1).2, (pieces hm (-1)).2,
    hmi, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

open GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixGen

theorem ofReal_dens_trans {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) (c c' : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) :
    ENNReal.ofReal ((ε : ℤ) * dens L c y) =
      ENNReal.ofReal (‖transDet c.e c'.e y‖ ^ 2) * ENNReal.ofReal ((ε : ℤ) * dens L c' y) := by
  rw [_root_.GlobalTheory.Mix.ChartChange.dens_change_chart k X p σ D L c c' y hy hy', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem map_part {k K : Type} [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] {X G : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) {D : ℕ} (hX : IsArithVar p D)
    (L : Fin D → MLine p (τ.comp (algebraMap k K))) (ε : ℤˣ) :
    Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε := by
  have hm : IsHomeomorph (bcPt hp.w τ) := _root_.GlobalTheory.Mix.isHomeomorph_bcPt k K (algebraMap k K) X G p q j hp τ
  obtain ⟨_, hT2, hSC⟩ := (IsArithVar.finite_emb_and_topology hX).2 (τ.comp (algebraMap k K))
  let h := hm.homeomorph (bcPt hp.w τ)
  haveI : T2Space (CxPts q τ) := h.isEmbedding.t2Space
  haveI : SecondCountableTopology (CxPts q τ) := h.isEmbedding.secondCountableTopology
  obtain ⟨hGi, _, _, _, hgen, _⟩ := GlobalTheory.Mix.genericFibre_facts k K X G p q j hp D hX
  obtain ⟨U, hU, hηU, t, ht⟩ := GenericCoords.exists_affine_etale_coords hX
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hηU
  have hTc : IsClosed {y : CxPts p (τ.comp (algebraMap k K)) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
    have e : {y : CxPts p (τ.comp (algebraMap k K)) | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} =
        (ptsIn p (τ.comp (algebraMap k K)) U)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [e]
    exact (isOpen_ptsIn _).isClosed_compl
  have hZG : IsClosed (j ⁻¹' (U : Set X)ᶜ) := hZ.preimage j.continuous
  have hgZG : genericPoint G ∉ j ⁻¹' (U : Set X)ᶜ := by
    simp only [Set.mem_preimage]
    rw [hgen]
    exact hgZ
  have key := GlueCoverNull.map_glueMeas_of_cover D (CxPts p (τ.comp (algebraMap k K))) (CxPts q τ)
    (AlgChart p (τ.comp (algebraMap k K)) D) (AlgChart q τ D) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).bc hp.w τ) c y))
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans L ε c c' y hy hy')
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans _ ε c c' y hy hy')
    (bcPt hp.w τ) hm.continuous _ hTc (fun c => ChernNull.chart_null hX hZ hgZ _ c)
    (fun c => ChernNull.chart_null_field K G q τ D _ hZG hgZG c) 1
    (fun x _ => by
      obtain ⟨w0, hw0⟩ := hm.surjective x
      exact Set.encard_eq_one.2 ⟨w0, Set.ext fun w =>
        ⟨fun hw => hm.injective (hw.trans hw0.symm), fun hw => hw ▸ hw0⟩⟩)
    (fun z hz => by
      have hmem : bcPt hp.w τ z ∈ ptsIn p (τ.comp (algebraMap k K)) U := by
        simpa [mem_ptsIn] using hz
      obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU t ht hmem
      obtain ⟨c', hz', hc'⟩ := GlobalTheory.Mix.exists_chart_dens_bc k K (algebraMap k K) X G p q j hp τ D c z hc
      exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2.1, by simp only [(hc' w hw).2.2 L]⟩⟩)
  rw [Nat.cast_one, one_smul] at key
  exact key

theorem part_int_generic : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  intro k K _ _ _ _ X G _ p q j hp τ D hX L
  have hmap := map_part hp τ hX L
  have hm : IsHomeomorph (bcPt hp.w τ) := _root_.GlobalTheory.Mix.isHomeomorph_bcPt k K (algebraMap k K) X G p q j hp τ
  have he : MeasurableEmbedding (bcPt hp.w τ) := (hm.homeomorph (bcPt hp.w τ)).measurableEmbedding
  refine ⟨hmap, fun f => ⟨?_, ?_⟩⟩
  · simp only [Intg]
    rw [← hmap 1, ← hmap (-1), he.integrable_map_iff, he.integrable_map_iff]
    rfl
  · simp only [Mix.int]
    rw [← hmap 1, ← hmap (-1), he.integral_map, he.integral_map]

end GlobalTheory.MixGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSumDegenerationDataFstCubeIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)), wM.IsGen → (∃ b₁ b₂, MapsAt₂ wM (eSec D.toPre.P.A) 1 D.toPre.rig b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ D₁.toPre.rig ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ D₂.toPre.rig) → (∀ x, ∃ b₁ b₂, MapsAt₂ wM (D.toPre.xK x) (-1) (D.toPre.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.toPre.P.L _ _ _ _ b₁ (D₁.toPre.psi (q₁ x)) ∧ LB.Gen.Corr D₂.toPre.P.L _ _ _ _ b₂ (D₂.toPre.psi (q₂ x))) → ∀ (w : LB.Iso (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L) (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L)), (∀ (Z : Scheme.{0}) (f : Z ⟶ (D₁.toPre.P.A ⊗ D.toPre.P.A).left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → D₁.toPre.P.L.ι) (jA : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι) (β : ULift.{0} (Finset (Fin 2)) → D₂.toPre.P.L.ι), f z ∈ (cubeLB D₁.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] D₁.toPre.P.L).U jC → f z ∈ (cubeLB D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] D.toPre.P.L).U jA → (∀ I, (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left ≫ p₂.left) z ∈ D₂.toPre.P.L.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum D.toPre.P.A ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card))) → ∀ (y : D₁.toPre.X) (y' : D.toPre.X) (z : (TK R).left) (J₁ : ((TK R).left ⟶ D₁.toPre.P.A.left) → D₁.toPre.P.L.ι) (J₂ : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D₁.toPre.P.L z J₁ → Good D.toPre.P.L z J₂ → val ((pol D).tau (j₁ y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ D₁.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left z J₁ J₂ * val ((pol D₁).tau y (q₁ y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumProd.tau_sum_fst | exact GlobalTheory.MumProd.tau_sum_fst | (intros; apply GlobalTheory.MumProd.tau_sum_fst <;> assumption)
end

