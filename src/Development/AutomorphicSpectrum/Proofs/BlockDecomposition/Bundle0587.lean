module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemNormsOfCongrEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} {X Y H : Matrix (Fin n) (Fin n) K}
    (h : X * H = H * Y) (p : K[X]) : aeval X p * H = H * aeval Y p := by
  have hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc,
      Algebra.commutes a H, Matrix.mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_norms_of_congr (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q)
    (hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e)
    (hιc : ∀ y, involBase Q k (ι y) = ι (cj w y))
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = eval₂ ι ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := Matrix.charpoly_map _ _
  obtain ⟨f, hf⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    exact this
  have hHu : IsUnit H.det := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet.isUnit).map _
  have hcT : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀)) := by
      rw [GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]
    have h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
      rw [hc2, hf, h1, Matrix.mul_assoc]
    have h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f := by
      have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hHu
      calc aeval A m = H⁻¹ * H * aeval A m := by rw [hHi, Matrix.one_mul]
        _ = H⁻¹ * H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
          rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
        _ = _ := by rw [hHi, Matrix.one_mul]
    rw [map_sub, map_mul, ← h3, sub_self]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t := by
    rw [← ht]; ring
  have h0 : Φ (atPl w γ₀.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) := by
    rw [hinvΦ, ← map_mul, hft, map_add (f := _), map_mul, h0, zero_mul, add_zero, hx]
    rfl
  have hu : IsUnit (Φ f) :=
    isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)
  exact ⟨hu.unit, Units.ext hz⟩

theorem mem_norms_of_congr_equiv (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (j : w.adicCompletion E ≃+* k ⊗[maximalRealSubfield E] E)
    (hj1 : ∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e)
    (hj2 : ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) =
      eval₂ (((inclBase Q k).toRingHom).comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  refine mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx
  · change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  · change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.CompanionTheory.NormCongr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinates
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mchart_zero (n : Fin 1 → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : k = 0 := Fin.fin_one_eq_zero k
  exact hx

theorem mchart_succ {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) :
    mchart c = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) := by
  apply TopologicalSpace.Opens.ext
  ext x
  refine ⟨fun hx => ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 hx j.succ⟩,
    fun hx => Set.mem_iInter.2 fun k => ?_⟩
  induction k using Fin.cases with
  | zero => exact hx.1
  | succ j => exact Set.mem_iInter.1 hx.2 j

theorem multiprojectivePoint_fst {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (ptP (n 0) (c 0) (fun i => z ⟨0, i⟩)).1 :=
  GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ 0

theorem multiprojectivePoint_snd {m : ℕ} (n : Fin (m + 2) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (multiprojectivePoint c z).1 ≫ pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) =
      (multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩)).1 :=
  pullback.lift_snd _ _ _

theorem multiprojective_chart_affine_holomorphic_points (m : ℕ) : ∀ (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c)) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  induction m with
  | zero =>
    intro n c
    have key : ∀ W : (MP ℤ 0 n).Opens, W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ 0 n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ 0 n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ 0 n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      have hpt : ∀ z : (Σ k, Bk n k) → ℂ, multiprojectivePoint c z = ptP (n 0) (c 0) (fun i => z ⟨0, i⟩) := fun z => rfl
      refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), fun z _ => ?_, fun a => ?_⟩
      · rw [hpt]
        exact CxPts.ofHom_mem _ _ _
      · have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
          differentiable_pi.2 fun i => differentiable_apply _
        exact (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL.differentiableOn fun z hz => hz 0
    exact key _ (mchart_zero n c)
  | succ m ih =>
    intro n c
    obtain ⟨hA, hM, hD⟩ := ih (Fin.tail n) (fun j => c j.succ)
    have hL : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩) :=
      differentiable_pi.2 fun p => differentiable_apply _
    have hL0 : Differentiable ℂ (fun (z : (Σ k, Bk n k) → ℂ) (i : Fin (n 0 + 1)) => z ⟨0, i⟩) :=
      differentiable_pi.2 fun i => differentiable_apply _
    have hT : Set.MapsTo (fun (z : (Σ k, Bk n k) → ℂ) (p : Σ k, Bk (Fin.tail n) k) => z ⟨p.1.succ, p.2⟩)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
        {z : (Σ k, Bk (Fin.tail n) k) → ℂ | ∀ k, z ⟨k, c k.succ⟩ ≠ 0} := fun z hz k => hz k.succ
    have main := GlobalTheory.CompanionTheory.Ar.ProdHolo.differentiableOn_ev_prod (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) σ₀
      {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} (chart ℤ (n 0) (c 0))
      (mchart (n := Fin.tail n) (fun j => c j.succ))
      (isAffineOpen_chart ℤ (n 0) (c 0)) hA
      (fun z => ptP (n 0) (c 0) (fun i => z ⟨0, i⟩))
      (fun z => multiprojectivePoint (n := Fin.tail n) (fun j => c j.succ) (fun p => z ⟨p.1.succ, p.2⟩))
      (multiprojectivePoint c) (multiprojectivePoint_fst n c) (multiprojectivePoint_snd n c)
      (fun z _ => CxPts.ofHom_mem _ _ _) (fun z hz => hM _ (hT hz))
      (fun a => (GlobalTheory.CompanionTheory.MPSmooth.differentiableOn_ev_ptP (n 0) (c 0) a).comp hL0.differentiableOn fun z hz => hz 0)
      (fun b => (hD b).comp hL.differentiableOn hT)
    have key : ∀ W : (MP ℤ (m + 1) n).Opens,
        W = (pullback.fst (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
          pullback.snd (PSpace.str ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
            mchart (n := Fin.tail n) (fun j => c j.succ) : (MP ℤ (m + 1) n).Opens) → IsAffineOpen W ∧
        (∀ z ∈ {z : (Σ k, Bk n k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0}, multiprojectivePoint c z ∈ ptsIn (mpStr ℤ (m + 1) n) σ₀ W) ∧
        ∀ a : Γ(MP ℤ (m + 1) n, W), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ (m + 1) n) σ₀ W a ∘ multiprojectivePoint c)
          {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      rintro W rfl
      exact main
    exact key _ (mchart_succ n c)

theorem mchart_affine_holo : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k), IsAffineOpen (mchart c) ∧
    ∀ a : Γ(MP ℤ m n, mchart c), DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c)
      {z | ∀ k, z ⟨k, c k⟩ ≠ 0} :=
  fun m n c => ⟨(multiprojective_chart_affine_holomorphic_points m n c).1, (multiprojective_chart_affine_holomorphic_points m n c).2.2⟩

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquiv
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypInert

open GlobalTheory.CompanionTheory.LocInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cjv_apply (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X, evR_apply, evR_apply]
  change pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv X) = cj w (pLoc E w X)
  rw [pLoc_conjFin]
  exact GlobalTheory.BCT.GlobLev.conjLoc_eq_cj hw X

theorem evY_thv (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem inert_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := by
  intro hC E _ _ _ a b v w hw
  obtain ⟨w, rfl⟩ := w
  exact ⟨evY hw a b, evY_apply hw a b, evY_thv hC hw a b, mem_Kv_iff hw a b⟩

end GlobalTheory.CompanionTheory.LocHypInert

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuousStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_involution_continuous : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
  Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧ ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | exact GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.sgP_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditive
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd

theorem psiFin_add' (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
    simp only [pairA]
    exact Prod.ext (add_zero 0).symm rfl
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem hR_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem hR_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem pairB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  intro F E _ _ _ _ _ σ M J n ψ b
  have hg1 : ∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J (X + X') Y = gram2 σ J X Y + gram2 σ J X' Y := by
    intro X X' Y
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_left _ σ J _ _ _
  have hg2 : ∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J X (Y + Y') = gram2 σ J X Y + gram2 σ J X Y' := by
    intro X Y Y'
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_right _ σ J _ _ _
  refine ⟨fun X X' Y => ?_, fun X Y Y' => ?_⟩
  · simp only [pairB, hg1, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']
  · simp only [pairB, hg2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_mem_blockChart (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) :
    ∃ i, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) :=
  ⟨ptChart _ k, GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩

theorem exists_ne_zero_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (k : Fin (m + 1)) : ∃ i, z ⟨k, i⟩ ≠ 0 :=
  (exists_mem_blockChart w k).imp fun i hi => (h k i).1.1 hi

theorem sameOrbit_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z z' : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (h' : IsUnder w z') : SameOrbit z z' := by
  choose c hc using exists_mem_blockChart w
  refine ⟨fun k => z ⟨k, c k⟩ / z' ⟨k, c k⟩,
    fun k => div_ne_zero ((h k _).1.1 (hc k)) ((h' k _).1.1 (hc k)), ?_⟩
  funext ⟨k, j⟩
  have e := ((h k (c k)).2 j (hc k)).symm.trans ((h' k (c k)).2 j (hc k))
  have a := (h k _).1.1 (hc k)
  have b := (h' k _).1.1 (hc k)
  rw [div_eq_div_iff a b] at e
  show z ⟨k, j⟩ = z ⟨k, c k⟩ / z' ⟨k, c k⟩ * z' ⟨k, j⟩
  rw [div_mul_eq_mul_div, eq_div_iff b]
  linear_combination e

theorem eq_iff_sameOrbit (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ)
    (h : IsUnder (PtsOver.map i rfl _ y) z) (h' : IsUnder (PtsOver.map i rfl _ y') z') :
    y = y' ↔ SameOrbit z z' := by
  constructor
  · rintro rfl
    exact sameOrbit_of_isUnder h h'
  · intro ho
    have e := (Under.existsUnique_isUnder m n z (exists_ne_zero_of_isUnder h)).unique h
      (isUnder_of_sameOrbit m n _ z' z h' ho)
    exact Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val e))

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

