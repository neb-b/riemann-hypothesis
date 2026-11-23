module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroVacuumBesselLineLatticeRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LineZero

variable {D : D7}

theorem rat_mul_mem_latO_neg {V T T' : HSp D} {LS : Set (Fin V.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hq : ∀ t ∈ LT, q *ᵥ t ∈ LT') :
    ∀ x ∈ latO (negSp V) T LS LT P, rat q ⬝ x ∈ latO V T' LS (LT' : Set _) P := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨α, hα, hv, a, ha, s, hs, -(q *ᵥ t), neg_mem (hq t ht), ?_⟩
    ext i j
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply]
    have e : ∀ (e : D.host.E) (u : AF D.host.F) (c : D.host.E), incA D e * (u ⊗ₜ[D.host.F] c) = u ⊗ₜ[D.host.F] (e * c) := by
      intro e u c
      show (Algebra.TensorProduct.includeRight e : AF D.host.F ⊗[D.host.F] D.host.E) * _ = _
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e, ← TensorProduct.tmul_sum]
    congr 1
    have hX : ∑ k, star (s k) * (negSp V).gram k j = -∑ k, star (s k) * V.gram k j := by
      simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hX]
    generalize (∑ k, star (s k) * V.gram k j) = X
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem exists_vacG_lineLat_zero : OnStd fun {D} _ _ _ {G} W F => ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have hq0 : ∀ t ∈ (G.Λ (.core 0) : Set (Fin (G.V (.core 0)).rank → D.host.E)),
      F.oz.qB *ᵥ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
    intro t ht
    have ht' : t ∈ G.sp.dec0.lat (L.ΛY 0) fun _ => 1 := by rw [← G.sp.lat0]; exact ht
    obtain ⟨y, -, u, hu, rfl⟩ := ht'
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
    have ha : G.sp.dec0.a *ᵥ u = u 0 • (F.oz.iB *ᵥ F.ζ 0) := by
      rw [hF.zB]
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [Matrix.mulVec_add, ha, Matrix.mulVec_smul, ← hF.zA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F.oz.qB_iA,
      F.oz.qB_iB, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  have hLT : IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    have hs : Subsingleton (Fin F.Lz.rank) := by rw [F.rk]; infer_instance
    have hne : Nonempty (Fin F.Lz.rank) := ⟨⟨0, by rw [F.rk]; omega⟩⟩
    let B : Matrix (Fin F.Lz.rank) (Fin F.Lz.rank) D.host.E := Matrix.of fun i _ => F.ζ 0 i
    let f : Fin F.Lz.rank → Fin 1 := fun _ => 0
    have hiB : F.oz.iB * B = G.sp.dec0.a.submatrix id f := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hF.zB i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.mul_apply, B, Matrix.of_apply, Matrix.submatrix_apply, id, f]
      exact this
    have hB : Bᴴ * F.Lz.gram * B = 1 := by
      rw [← F.oz.isoB]
      have e : Bᴴ * (F.oz.iBᴴ * (G.V (.core 0)).gram * F.oz.iB) * B =
          (F.oz.iB * B)ᴴ * (G.V (.core 0)).gram * (F.oz.iB * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [e, hiB]
      refine (G.sp.dec0.gram_sub f f).trans (Matrix.ext fun i j => ?_)
      rw [Subsingleton.elim i j]
      simp [antiDiagonalSignGramMatrix, f]
    have hB' : B * (Bᴴ * F.Lz.gram) = 1 := mul_eq_one_comm.1 hB
    let Bg : GL (Fin F.Lz.rank) D.host.E := ⟨B, Bᴴ * F.Lz.gram, hB', hB⟩
    have hc : IsSelfDualC F.Lz (Formalism.L2.DIV.colLat Bg) :=
      GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal F.Lz Bg hB
    have hcs : Formalism.L2.DIV.colLat Bg = Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
      unfold Formalism.L2.DIV.colLat
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rfl
      · rintro rfl; exact ⟨Classical.arbitrary _, rfl⟩
    rw [hcs] at hc
    exact isSelfDualC_neg hc
  have hLS : IsSelfDualC (G.V (.core 1)) (G.Λ (.core 1)) := (G.sp.P_is 1 (by have := D.R.two_le_m; omega)).sd
  have hle : lineLat F 0 ≤ latO (G.V (.core 1)) (negSp F.Lz) (G.Λ (.core 1) : Set _)
      (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) (fun _ => True) := by
    intro b hb
    rw [lineLat] at hb
    have hb' : F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b ∈ latCore G 0 := hb
    have e : b = rat F.oz.qB ⬝ (F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      change b = F.oz.pB ⬝ F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.pB ⬝ F.oz.jB ⬝ b
      rw [OrthDec.pB_jA, OrthDec.pB_jB, Matrix.mul_zero, zero_add, Matrix.one_mul]
    rw [e]
    exact rat_mul_mem_latO_neg (V := G.V (.core 1)) F.oz.qB hq0 _ hb'.1
  exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ _ _ hLS hLT _ hle

end GlobalTheory.AscFin.LineZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (g : GA D S) (h : GA D T) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      N • actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D))
    ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  rw [← smul_smul]
  apply hKt
  · have h0 := GlobalTheory.SplitScalar.latO_fin hu
    have hz : (actO S T g h u).map (infPart D) = 0 := by
      simp only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have hij := congrFun (congrFun hz i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢
    rw [hij, smul_zero]
  · intro i j
    have hX := hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j
    have e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) *
        ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j := by
      simp only [actO]
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    rw [e1]
    exact hX

theorem isSBHalf_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) {a : AE D}
    (g : GA D S) (h : GA D T) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) fun t => Φ (actO S T g h t) := by
  simp only [IsSBHalf] at hΦ ⊢
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  obtain ⟨N, hN, hNu⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨M, hM, hMu⟩ := exists_nsmul_actO hS hT g⁻¹ h⁻¹
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩
  · intro u hu hua t
    rw [act_add, act_nsmul]
    have hw := hNu u hu
    have hwa : IsHalf a (N • actO S T g h u) :=
      GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N
    have e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _
  · intro t ht
    have hm := hMu _ (h3 _ ht)
    rw [act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO] at hm
    have e : (k * (N * M)) • t = N • (M • (k • t)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact AddSubgroup.nsmul_mem _ hm N

theorem absV_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : (Fv F v)ˣ) :
    absV F v (x * y) = absV F v x * absV F v y := by
  unfold absV
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]

theorem absFin_mul (x y : (AE D)ˣ) : absFin D (x * y) = absFin D x * absFin D y := by
  unfold absFin
  simp_rw [map_mul, absV_mul]
  exact finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)

theorem absFin_one : absFin D 1 = 1 := by
  have h := absFin_mul (D := D) 1 1
  rw [mul_one] at h
  have hp := absFin_pos D 1
  have h2 : absFin D 1 * (absFin D 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

theorem modFac_mul (x x' y y' : (AE D)ˣ) : modFac S T (x * x') (y * y') = modFac S T x y * modFac S T x' y' := by
  unfold modFac
  rw [absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le,
    Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]
  ring

theorem modFac_one : modFac S T 1 1 = 1 := by
  unfold modFac
  rw [absFin_one, Real.one_rpow, Real.one_rpow, one_mul]

end GlobalTheory.SplitLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSummandEmbeddingHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add (f := _), add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add (f := _), mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))


variable (G) in
theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h


variable (G) in
theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)


variable (G) in
theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_left ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dite_eq_right (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowTheta

theorem isThetaFunO_cosVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.cosVec i κ) := by
  obtain ⟨e, -, h⟩ := W.cosVec_is
  exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) (W.vac_is i hi).2.2

theorem isThetaFunO_datum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (isThetaFunO_cosVec W i i.2 (Φ i)) (ρ i)

end GlobalTheory.RowTheta

theorem GlobalTheory.RowTheta.rowDatum_isThetaFunO : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ Φ i =>
    GlobalTheory.RowTheta.isThetaFunO_datum ch.W ch.ρ Φ i⟩⟩

end
end

