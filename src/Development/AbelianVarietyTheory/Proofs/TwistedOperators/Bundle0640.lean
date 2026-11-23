module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : idLat 1 Λ = Λ := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem idLat_mulVec {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ := by
  intro x hx
  have hle : idLat I Λ ≤ (idLat I Λ).comap ((Matrix.mulVecLin M).restrictScalars (𝓞 D.host.E)) := by
    rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    change M *ᵥ (s • y) ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨s, hs, M *ᵥ y, hM y hy, rfl⟩
  exact hle hx

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

section Witt

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pX_jX)
theorem qX_e' : d.qX * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_jY)
theorem qX_i₀ : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
theorem qY_e : d.qY * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_jX)
theorem qY_e' : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
theorem qY_i₀ : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)

end Witt

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem mul_col {m n r c : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E)
    (Bm : Matrix (Fin n) (Fin r) D.host.E) (q : Fin c) (p : Fin r) (κ : D.host.E) (h : ∀ l, a l q = κ * Bm l p)
    (k : Fin m) : (M * a) k q = κ * (M * Bm) k p := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ)

theorem auxiliary_vector_multiple_of_witt_basis_vector (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (q : Fin c) :
    (q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e l p) ∧
    (¬ q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e' l p) := by
  obtain ⟨h2, he, s, he'⟩ := hd
  have hq2 := q.2
  refine ⟨fun hq => ⟨⟨q.1, hq⟩, ((-D.host.xi0) ^ (q.1 + 1))⁻¹, fun l => ?_⟩, fun hq => ?_⟩
  · rw [he]
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))]
    rfl
  · have hp : c - 1 - q.1 < ρ := by omega
    have hs : s ⟨c - 1 - q.1, hp⟩ ≠ 0 := by
      intro h0
      have := congrFun (congrFun (qY_e' d) ⟨c - 1 - q.1, hp⟩) ⟨c - 1 - q.1, hp⟩
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp [he', colsOf, h0] at this
    refine ⟨⟨c - 1 - q.1, hp⟩, (s ⟨c - 1 - q.1, hp⟩)⁻¹, fun l => ?_⟩
    rw [he']
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ hs]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_castLE]
    omega

theorem wittHyperbolic_projX_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e * d.qX * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qX_e, Matrix.mul_one, if_pos hq, mul_one, h]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qX_e', hq]

theorem wittHyperbolic_projY_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e' * d.qY * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qY_e, hq]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qY_e', Matrix.mul_one, if_neg hq, mul_one, h]

theorem proj_lat (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (hi : d.i₀ = frameMat B A a.ι)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    ∀ x ∈ a.lat Λ 𝔟, (d.e * d.qX) *ᵥ x ∈ a.lat Λ 𝔟 ∧ (d.e' * d.qY) *ᵥ x ∈ a.lat Λ 𝔟 := by
  rintro x ⟨y, hy, u, hu, rfl⟩
  have k1 : d.e * d.qX * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qX_i₀, Matrix.mul_zero]
  have k2 : d.e' * d.qY * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qY_i₀, Matrix.mul_zero]
  refine ⟨⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) *ᵥ u, fun p => ?_, ?_⟩,
    ⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) *ᵥ u, fun p => ?_, ?_⟩⟩
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [one_mul]; exact hu p
    · rw [zero_mul]; exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k1, wittHyperbolic_projX_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [zero_mul]; exact (𝔟 p).zero_mem
    · rw [one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k2, wittHyperbolic_projY_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

end SlopeTestRemainingChoices

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin


open GlobalTheory.AscFin.BigProj in
theorem pcBF_big_core : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)),
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) →
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h w hw
  have sdS : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdT : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdB := ((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have big : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := by
    have key := _root_.GlobalTheory.DepthShift.mem_latO_shift hq μ0 hL G (S := G.V (.grid (2 * ρ + 2) 0)) (B := G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0)) 1 (G.Λ (.grid (2 * ρ + 1) 0)) sdS (by rw [idLat_one]; exact sdT)
      (by rw [one_mul]; exact sdB) _ (by rw [idLat_one]; exact latO_negSp_le _ _ _ _ _ hw.1)
      ⟨e, he, by rw [idLat_one]; exact hw.2 e he⟩
    rw [one_mul] at key
    exact key
  have h1 : 1 ≤ 2 * ρ + 1 := by omega
  have h2 : 2 * ρ + 1 ≤ D.R.m := by omega
  have hlat : ∀ x ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).e * (F.dJ ρ h).qX) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) ∧
      ((F.dJ ρ h).e' * (F.dJ ρ h).qY) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
    have e1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) h1 h2).lat (G.sp.P (2 * ρ + 1)).lat
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) h1 h2
    rw [e1]
    exact proj_lat _ _ (hF.hJ ρ h) (by omega) (hF.aJ ρ h) _ _
  have sdS' : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) := sdS
  have hx := _root_.GlobalTheory.Twist.RatLatO.rat_mul_mem_latO sdS' sdS' sdB 1 ((F.dJ ρ h).e * (F.dJ ρ h).qX)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).1) _ big
  have hy := _root_.GlobalTheory.Twist.RatLatO.rat_mul_mem_latO sdS' sdS' sdB 1 ((F.dJ ρ h).e' * (F.dJ ρ h).qY)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).2) _ big
  have hr1 : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, x ⬝ rat 1 = x := fun x => by
    rw [rat_one]; exact Matrix.mul_one x
  have ex : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) =
      (rat ((F.dJ ρ h).e * (F.dJ ρ h).qX) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc]
    rfl
  have ey : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) =
      (rat ((F.dJ ρ h).e' * (F.dJ ρ h).qY) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc]
    rfl
  exact ⟨ex ▸ hx, ey ▸ hy⟩

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMoved
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColVac

variable {D : D7} {T : Type}

theorem xi_mem_xiVals {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (x : (AE D)ˣ) :
    Circle.toUnits (L.xi t x) ∈ xiVals L t := by
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e : L.xi t x = L.xi t (b x) := by
    conv_lhs => rw [hab x, map_mul, GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (ha x).2, one_mul]
  rw [e]
  have hx := (hb x).1
  generalize b x = u at hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 _ _ (hL.xi t)
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (u : AE D)), ι (finPart D ((u⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod u hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  have h6 : Circle.toUnits (L.xi t u) = ∏ P ∈ S, (L.xiH t).locK P (k P) := by
    apply Units.ext
    rw [Units.coe_prod]
    exact h5
  rw [h6]
  exact prod_mem fun P _ => Subgroup.subset_closure ⟨P, _, rfl⟩

theorem attChr_mu {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (j n : ℕ) :
    Formalism.IndefR.Lift.attChr (L.mu t j) L.eta n = Formalism.IndefR.Lift.attChr (L.mu μ0 j) L.eta n * L.xi t := by
  have hb : L.xi μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ0))
  have e : L.mu t j = L.mu μ0 j * L.xi t := by
    show L.mu0 j * L.xi t = L.mu0 j * L.xi μ0 * L.xi t
    rw [hb, mul_one]
  unfold Formalism.IndefR.Lift.attChr
  rw [e]
  split_ifs
  · exact mul_right_comm _ _ _
  · rfl

section Move

variable {V : HSp D} {k : GA D V} {C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}


set_option synthInstance.maxHeartbeats 400000 in
theorem fwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (h _).1 (Submodule.subset_span ⟨s, hs, rfl⟩)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  have e2 : (Formalism.IndefR.Lev.finE V k).1 * (Formalism.IndefR.Lev.finE V k⁻¹).1 = 1 :=
    congrArg Units.val (((Formalism.IndefR.Lev.finE V).map_mul k k⁻¹).symm.trans
      ((congrArg (Formalism.IndefR.Lev.finE V) (mul_inv_cancel k)).trans (Formalism.IndefR.Lev.finE V).map_one))
  rw [GlobalTheory.MovedHomLat.bridge]
  refine (h _).2 ?_
  rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

end Move

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U}

theorem isVac_moved (Z : Normal W N) (t : T) {j : ℕ} (hj : j < D.R.m) :
    W.IsVac (.top t j) (W.om (.top t j) ((N.u (.top j)).1, (N.u (.top (j + 1))).1) (Z.vac (.top t j))) := by
  have h0 := N.u_lat (.top j) hj.le
  have h1 := N.u_lat (.top (j + 1)) hj
  have H := GlobalTheory.MovedHomLat.actO_latO_onto (G.V (.top j)) (G.V (.top (j + 1))) (N.u (.top j)).1 (N.u (.top (j + 1))).1
    _ _ _ _ (fwd h0) (fwd h1) (bwd h0) (bwd h1)
  refine GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)) W.θ_is
    _ _ _ _ _ _ _ _ _ _ (fun τ => ?_) (fun τ => ?_) (fun u => ⟨fun hu => ?_, ?_⟩) _ (Z.vac_is (.top t j) hj)
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top j)).2, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top (j + 1))).2, Matrix.mul_one, Matrix.one_mul]
  · obtain ⟨w, hw, e⟩ := H.2 u hu
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact H.1 w hw

theorem colVac : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch _
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  choose x hx using fun j => GlobalTheory.RecDict.exists_isDetRoot D (ch.G.V (.top j)) (ch.S.N.u (.top j)).1
  refine ⟨fun j => ch.W.om (.top A.μ0 j) ((ch.S.N.u (.top j)).1, (ch.S.N.u (.top (j + 1))).1) (ch.S.Z.vac (.top A.μ0 j)),
    fun t j hj => isVac_moved ch.S.Z A.μ0 hj, fun _ => 1,
    fun t j => Circle.toUnits (R.toLevCh.xi t ((x j)⁻¹ * x (j + 1))),
    fun t j => xi_mem_xiVals hL t _, fun t j hj => ?_⟩
  have hW0 := ch.W.om_is (.top A.μ0 j) (show j + 1 ≤ D.R.m from hj)
  have hWt := ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have eS : ch.G.chrS (.top t j) = ch.G.chrS (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  have eT : ch.G.chrT (.top t j) = ch.G.chrT (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  rw [eS, eT] at hWt
  have e := GlobalTheory.TupRoot.twist_eq hW0 hWt (hx j) (hx (j + 1)) (ch.S.Z.vac_is (.top A.μ0 j) hj).2.theta
  rw [(ch.S.Z.free t A.μ0 j).2.1]
  refine e.trans ?_
  congr 1
  rw [one_mul, ← MonoidHom.map_inv, ← MonoidHom.map_mul]
  rfl

end GlobalTheory.ColVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def locAt (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  (inBasis (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w).comp (Lev.finE _)

theorem locAt_inf (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) {a : GA D (G.V (.grid D.R.m j))}
    (ha : a ∈ GinfC _) : locAt B t w j hj a = 1 := by
  have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
    simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.comp_apply, ha, map_one]
  simp only [locAt, MonoidHom.comp_apply, h, map_one]

theorem exists_isFinOf (V : HSp D) (g : GA D V) : ∃ b, GlobalTheory.RowVal.IsFinOf g b := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨p, rfl⟩ := e.surjective g
  exact ⟨p.2, p.2.2, p.1, p.1.2, (he p).symm⟩

theorem elt_succ (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (i : Fin ((locGrid G t w).m - 2)) :
    (repsAt G t w).elt β ((locGrid G t w).m, i.1 + 1) = (repsAt G t w).rep i (β i) := by
  simp only [Reps.elt]
  rw [onColumn_apply]
  simp only [dif_pos i.2]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem loc_rep (B : Frames G) (t : T) (s : ℤˣ) (β : CosFam G t) (w : locPl G t) (i : Fin ((locGrid G t w.1).m - 2))
    (hj : i.1 + 1 ≤ D.R.m) (r : GA D (G.V (.grid D.R.m (i.1 + 1))))
    (ρ : GL (Fin ((locGrid G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (hρ : ρ = (repsAt G t w.1).rep i (β w i))
    (hr : (inBasis (rank_vertex G t w.1 (X := (D.R.m, i.1 + 1)) ⟨le_rfl, hj⟩) (B.β D.R.m (i.1 + 1)) w.1)
      (Lev.finE (G.V (.grid D.R.m (i.1 + 1))) r) =
      GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * (repsAt G t w.1).elt (β w) (D.R.m, i.1 + 1)) :
    locAt B t w.1 (i.1 + 1) hj r = GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * ρ := by
  rw [hρ, ← elt_succ]
  exact hr

theorem mk_eq_of {Gp : Type} [Group Gp] (H K : Subgroup Gp) {A A' S X Y ρ ρ' : Gp}
    (e : A' * (S * ρ') = X * (A * (S * ρ)) * Y) (hN : (A' * S)⁻¹ * X * (A * S) ∈ H) (hY : Y ∈ K) :
    DoubleCoset.mk H K ρ = DoubleCoset.mk H K ρ' := by
  rw [DoubleCoset.eq]
  refine ⟨_, hN, Y, hY, ?_⟩
  rw [show (A' * S)⁻¹ * X * (A * S) * ρ * Y = (A' * S)⁻¹ * (X * (A * (S * ρ)) * Y) by group, ← e]
  group

theorem idx_le {j : ℕ} (h : j ∈ GlobalTheory.RowVal.idx D) : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  simp only [GlobalTheory.RowVal.idx, List.mem_range'_1] at h
  omega

end GlobalTheory.RowRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthLatticeLineComponentsMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineFB

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  obtain ⟨-, hfr, hline⟩ := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W M hM F hF
  have hx := AddSubgroup.mem_comap.1 hu
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply] at hx
  have hSc : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (G.isV (X := .core (2 * (σ + 1) + 1)) (by simp [Node.InRange]; omega) (fun j e => Node.noConfusion e)).sd
  have hSg : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hTg : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hℓ := (hfr σ h').2.2.1
  have hℓ' := hline (σ + 1)
  have h0 := (hfr σ h').1
  have hj : ∀ y ∈ G.Λ (.core (2 * (σ + 1) + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * (σ + 1) + 1) 0) :=
    GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits _ (_root_.GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all hSg) fun v => ((hfr (σ + 1) h).2.1 v).2
  have hq : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0), ((F.oB σ h').qB * (F.dB σ h').q0) *ᵥ t ∈
      idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec]
    exact _root_.GlobalTheory.FinPl.projB_mem_of_orthAt _ (_root_.GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all hℓ) (hfr σ h').2.2.2 _
      (_root_.GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits _ (_root_.GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all h0) (fun v => ((hfr σ h').2.1 v).1) t ht)
  have key : ((F.oB σ h').resT _ u).2 =
      rat ((F.oB σ h').qB * (F.dB σ h').q0) * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * rat (F.dJ (σ + 1) h).i₀ := by
    rw [OrthDec.resT_apply, rat_mul]
    change _ = (F.oB σ h').pB * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (F.dB σ h').p0, HypDec.p0_j0, Matrix.one_mul, HypDec.p0_j0, Matrix.mul_one]
  rw [key]
  have hz := _root_.GlobalTheory.Twist.RatLatO.rat_mul_mem_latO hSg hSc hℓ _ _ hj hq _ (latO_negSp_le' _ _ _ _ _ hx.1)
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hd := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom G.modul _ ((F.oB σ h').qB * (F.dB σ h').q0) hj hq _ (hx.2 e he)
  refine _root_.GlobalTheory.DepthShift.mem_latO_shift hD μ0 hL G _ _ _ hSc hℓ hℓ' _ hz ⟨e, he, ?_⟩
  rwa [Matrix.mul_smul, Matrix.smul_mul] at hd

end GlobalTheory.LineFB

end
end

