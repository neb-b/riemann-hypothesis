module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CoreSelfDual

variable {D : D7}

theorem form_eq (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem wittHyperbolicRankZero_proj_mul_emb (y : Fin S₀.rank → D.host.E) : d.q0 *ᵥ (d.i₀ *ᵥ y) = y := by
  have hq : d.q0 * d.i₀ = 1 := by
    calc d.q0 * d.i₀ = S₀.gram⁻¹ * (d.i₀ᴴ * S.gram * d.i₀) := by
          simp only [HypDec.q0, Matrix.mul_assoc]
      _ = 1 := by rw [d.iso]; exact Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀)
  rw [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec]

theorem wittCoreProjection_adjoint_coreEmbedding (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    star (d.q0 *ᵥ x) ⬝ᵥ S₀.gram *ᵥ y = star x ⬝ᵥ S.gram *ᵥ (d.i₀ *ᵥ y) := by
  have hM : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, GlobalTheory.MixModel.gramInv_conjTranspose, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀), Matrix.mul_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hM]

theorem isSelfDualC_comap {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ)
    (hP : ∀ x ∈ Λ, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ Λ) :
    IsSelfDualC S₀ (Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) := by
  unfold IsSelfDualC at hΛ ⊢
  obtain ⟨hlat, hdual⟩ := hΛ
  have hq : ∀ y, d.q0 *ᵥ (d.i₀ *ᵥ y) = y := GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb d
  have hmem : ∀ y, y ∈ Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ↔ d.i₀ *ᵥ y ∈ Λ :=
    fun y => Iff.rfl
  have heq : Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) =
      Λ.map ((Matrix.mulVecLin d.q0).restrictScalars (𝓞 D.host.E)) := by
    ext y
    rw [hmem, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, hq y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hP x hx
  refine ⟨?_, fun y => ?_⟩
  · rw [heq]
    exact Submodule.IsLattice.of_fg _ (hlat.fg.map _)
  · rw [hmem]
    constructor
    · intro hy x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := (hdual (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq, ← d.iso,
        Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · intro hy
      refine (hdual (d.i₀ *ᵥ y)).2 fun w hw => ?_
      obtain ⟨b, hb⟩ := hy (d.q0 *ᵥ w) (hP w hw)
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq,
        GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_adjoint_coreEmbedding]

theorem mulVec_col_eq_zero {n k c r : ℕ} {q : Matrix (Fin k) (Fin n) D.host.E} {a : Matrix (Fin n) (Fin c) D.host.E}
    {f : Fin r → Fin c} {s : Fin r → D.host.E} (h : q * colsOf a f s = 0) {p : Fin r} (hs : s p ≠ 0) :
    q *ᵥ (fun i => a i (f p)) = 0 := by
  funext i
  have h1 := congrFun (congrFun h i) p
  simp only [Matrix.mul_apply, colsOf, Matrix.zero_apply] at h1
  have h2 : s p * (q *ᵥ (fun i => a i (f p))) i = 0 := by
    rw [← h1]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact (mul_eq_zero.mp h2).resolve_left hs

theorem wittCoreProjection_kills_offMiddle_auxiliaryVectors {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1) (p : Fin c) (hp : p.1 ≠ ρ) :
    d.q0 *ᵥ (fun i => a.a i p) = 0 := by
  subst hc
  obtain ⟨h2, he, s, he'⟩ := h
  have hqe : d.q0 * d.e = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
  have hqe' : d.q0 * d.e' = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]
  rw [he] at hqe
  rw [he'] at hqe'
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe (p := ⟨p.1, hlt⟩) (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero))
    rw [show p = Fin.castLE (by omega) (⟨p.1, hlt⟩ : Fin ρ) from Fin.ext rfl]
    exact this
  · have hk : 2 * ρ - p.1 < ρ := by omega
    have hsk : s ⟨2 * ρ - p.1, hk⟩ ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun d.e'e ⟨2 * ρ - p.1, hk⟩) ⟨2 * ρ - p.1, hk⟩
      rw [he'] at h1
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, h0] at h1
    have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe' hsk
    rw [show p = (Fin.castLE (by omega) (⟨2 * ρ - p.1, hk⟩ : Fin ρ) : Fin (2 * ρ + 1)).rev from
      Fin.ext (by simp only [Fin.val_rev, Fin.coe_castLE]; omega)]
    exact this

private theorem mulVec_eq_sum_smul_col {R : Type} [CommRing R] {n c : ℕ} (M : Matrix (Fin n) (Fin c) R) (u : Fin c → R) :
    M *ᵥ u = ∑ p, u p • (fun i => M i p) := by
  funext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem proj_mem {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1)
    {N : Matrix (Fin S₀.rank) (Fin A.rank) D.host.E} (hN : d.i₀ * N = frameMat S A a.ι) {z : Fin S₀.rank → D.host.E}
    (hz : d.i₀ *ᵥ z = fun i => a.a i ⟨ρ, by omega⟩) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : Fin S.rank → D.host.E} (hx : x ∈ a.lat Λ 𝔟) :
    d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ a.lat Λ 𝔟 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  have hcol : ∀ p : Fin c, d.q0 *ᵥ (fun i => a.a i p) =
      if p = (⟨ρ, by omega⟩ : Fin c) then z else 0 := by
    intro p
    split_ifs with hp
    · have hpz : (fun i => a.a i p) = d.i₀ *ᵥ z := by rw [hz, hp]
      rw [hpz, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
    · exact GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_kills_offMiddle_auxiliaryVectors d a h hc p (fun e => hp (Fin.ext e))
  have h1 : d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y)) = frameMat S A a.ι *ᵥ y := by
    rw [← hN, ← Matrix.mulVec_mulVec, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
  have h2 : d.q0 *ᵥ (a.a *ᵥ u) = u ⟨ρ, by omega⟩ • z := by
    rw [mulVec_eq_sum_smul_col a.a u, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hcol, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show ∃ y' ∈ Λ, ∃ u' : Fin c → D.host.E, (∀ p, u' p ∈ 𝔟 p) ∧
    d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y + a.a *ᵥ u)) = frameMat S A a.ι *ᵥ y' + a.a *ᵥ u'
  refine ⟨y, hy, fun p => if p = (⟨ρ, by omega⟩ : Fin c) then u p else 0, fun p => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hu p
    · exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, Matrix.mulVec_smul, hz, mulVec_eq_sum_smul_col a.a]
    congr 1
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.AscFin.CoreSelfDual

namespace GlobalTheory.AscFin

theorem isSelfDualC_lat0 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G) (hF : Std F)
    (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have e : G.Λ (.grid (2 * ρ + 2) 0) =
      (G.colDec (2 * ρ + 2) h1 h).lat (G.Λ (.core (2 * ρ + 2))) (stairId _ _ _) :=
    G.sp.colLat (2 * ρ + 2) h1 h
  have hc : 2 * ρ + 2 - 1 = 2 * ρ + 1 := by omega
  show IsSelfDualC (F.V₀ ρ) ((G.Λ (.grid (2 * ρ + 2) 0)).comap
    ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E)))
  refine CoreSelfDual.isSelfDualC_comap (F.dB ρ h) (G.sp.V_is (2 * ρ + 2) 0 h1 h (Nat.zero_le _)).sd ?_
  intro x hx
  rw [e] at hx ⊢
  refine CoreSelfDual.proj_mem (F.dB ρ h) _ (hF.hB ρ h) hc (N := (F.oB ρ h).iA) (hF.aB ρ h)
    (z := (F.oB ρ h).iB *ᵥ F.ζ 0) ?_ hx
  rw [Matrix.mulVec_mulVec]
  exact hF.zB' ρ h

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdLatDual

variable {D : D7}

def hp (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E :=
  ∑ i, ∑ j, star (x i) * S.gram i j * y j

def IsO (z : D.host.E) : Prop := ∃ b : 𝓞 D.host.E, (b : D.host.E) = z

lemma isO_zero : IsO (0 : D.host.E) := ⟨0, by simp⟩
lemma isO_add {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z + w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩
lemma isO_mul {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z * w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩
lemma isO_coe (a : 𝓞 D.host.E) : IsO (a : D.host.E) := ⟨a, rfl⟩
lemma isO_star (a : 𝓞 D.host.E) : IsO (star (a : D.host.E)) := by
  refine ⟨⟨star (a : D.host.E), ?_⟩, rfl⟩
  exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom
lemma isO_of_mem_one {z : D.host.E} (h : z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : IsO z := by
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩

lemma osmul {n : ℕ} (a : 𝓞 D.host.E) (x : Fin n → D.host.E) : a • x = (a : D.host.E) • x := by
  ext i; simp [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]

variable (S : HSp D)

lemma hp_add_left (x x' y) : hp S (x + x') y = hp S x y + hp S x' y := by
  simp only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
lemma hp_add_right (x y y') : hp S x (y + y') = hp S x y + hp S x y' := by
  simp only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
lemma hp_zero_left (y) : hp S 0 y = 0 := by simp [hp]
lemma hp_zero_right (x) : hp S x 0 = 0 := by simp [hp]
lemma hp_smul_left (s : D.host.E) (x y) : hp S (s • x) y = star s * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
lemma hp_smul_right (t : D.host.E) (x y) : hp S x (t • y) = t * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.IdLatDual

open GlobalTheory.IdLatDual in
lemma GlobalTheory.IdLatDual.idLat_fg {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hΛ : Λ.FG)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (idLat I Λ).FG := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  let f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) := LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a
  have hle : (idLat I Λ).map f ≤ Λ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := hint s hs
    show a • (s • y) ∈ Λ
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj : Function.Injective f := by
    intro x x' h
    have h' : a • x = a • x' := h
    rw [osmul, osmul] at h'
    have : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    exact smul_right_injective _ this h'
  have hfg : ((idLat I Λ).map f).FG := Submodule.FG.of_le hΛ hle
  exact Submodule.fg_of_fg_map_injective f hinj hfg


open GlobalTheory.IdLatDual in
theorem GlobalTheory.idLat_isSelfDualC : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 →
    (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  intro D S Λ I I' hΛ hII' hconj
  obtain ⟨hlat, hdual⟩ := hΛ
  have intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y) := fun x hx y hy => (hdual y).1 hy x hx
  have gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ := fun s hs y hy =>
    Submodule.subset_span ⟨s, hs, y, hy, rfl⟩
  have one_mem : (1 : D.host.E) ∈ I * I' := by rw [hII']; exact FractionalIdeal.one_mem_one _

  have hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
    intro y hy
    have key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
  have hfg : (idLat I Λ).FG := idLat_fg Λ hlat.fg I
  refine ⟨Submodule.IsLattice.of_fg D.host.E hfg, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  ·
    have stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y) := by
      intro s hs x₀ hx₀ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, y₀, hy₀, rfl⟩ := hz
        rw [hp_smul_left, hp_smul_right, ← mul_assoc]
        refine isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)
        rw [← hII', mul_comm I]
        exact FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht
      | zero => rw [hp_zero_right]; exact isO_zero
      | add a b _ _ ha hb => rw [hp_add_right]; exact isO_add ha hb
      | smul c z _ hz => rw [osmul, hp_smul_right]; exact isO_mul (isO_coe c) hz
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, x₀, hx₀, rfl⟩ := hz
      obtain ⟨b, hb⟩ := stepA s hs x₀ hx₀ y hy
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩
    | add a b _ _ ha hb =>
      have h : IsO (hp S a y + hp S b y) := isO_add ha hb
      rw [← hp_add_left] at h
      exact h
    | smul c z _ hz =>
      obtain ⟨u, hu⟩ := isO_mul (isO_star c) hz
      exact ⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩
  · have hint : ∀ x ∈ idLat I Λ, IsO (hp S x y) := fun x hx => hy x hx
    have key : ∀ z ∈ I * I', z • y ∈ idLat I Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)
      · rw [mul_smul]
        refine gen i hi _ ((hdual _).2 fun x' hx' => ?_)
        have hsc : star c ∈ I := (hconj c).1 hc
        obtain ⟨b, hb⟩ := hint _ (gen _ hsc x' hx')
        refine ⟨b, ?_⟩
        rw [hb]
        show hp S (star c • x') y = hp S x' (c • y)
        rw [hp_smul_left, hp_smul_right, star_star]
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualStandardFrameLineLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem isSelfDualC_span_of_norm {D : D7} (S : HSp D) (hS : S.rank = 1) (ζ : Fin S.rank → D.host.E)
    (hζ : star ζ ⬝ᵥ (HSpace.gram S *ᵥ ζ) = -1) :
    IsSelfDualC S (Submodule.span (𝓞 D.host.E) {ζ}) := by
  have hform : ∀ x y : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * HSpace.gram S i j * y j = star x ⬝ᵥ (HSpace.gram S *ᵥ y) := by
    intro x y
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  obtain ⟨i₀, hi₀⟩ : ∃ i, ζ i ≠ 0 := Function.ne_iff.mp hne
  have hall : ∀ y : Fin S.rank → D.host.E, ∃ c : D.host.E, y = c • ζ := by
    intro y
    refine ⟨y i₀ / ζ i₀, funext fun i => ?_⟩
    rw [Subsingleton.elim i i₀, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi₀]
  have hpair : ∀ a c : D.host.E, star (a • ζ) ⬝ᵥ (HSpace.gram S *ᵥ (c • ζ)) = -(star a * c) := by
    intro a c
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hζ, smul_eq_mul, smul_eq_mul]
    ring
  have hstar : ∀ a : 𝓞 D.host.E, IsIntegral ℤ (star (a : D.host.E)) := fun a =>
    (map_isIntegral_int (starRingEnd D.host.E) a.2 : )
  refine ⟨⟨Submodule.fg_span_singleton _, ?_⟩, fun y => ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · obtain ⟨c, rfl⟩ := hall y
    constructor
    · intro hy x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hb, hform]
      refine ⟨-(⟨_, hstar a⟩ * b), ?_⟩
      have := hpair a b
      simp only [← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E b]
      rw [this]
      rfl
    · intro h
      obtain ⟨b, hb⟩ := h ζ (Submodule.mem_span_singleton_self _)
      have h1 := hpair 1 c
      rw [one_smul, star_one, one_mul] at h1
      rw [hform, h1] at hb
      refine Submodule.mem_span_singleton.mpr ⟨-b, ?_⟩
      rw [← algebraMap_smul D.host.E (-b)]
      congr 1
      rw [map_neg]
      exact neg_eq_iff_eq_neg.mpr hb

theorem isSelfDualC_line : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  intro D T L sc G F hF
  refine isSelfDualC_span_of_norm (negSp F.Lz) F.rk (F.ζ 0) ?_
  have h1 := congrFun (congrFun G.sp.dec0.gram 0) 0
  have h2 : star (fun i => G.sp.dec0.a i 0) ⬝ᵥ (HSpace.gram (G.V (Node.core 0)) *ᵥ (fun i => G.sp.dec0.a i 0)) = 1 := by
    have h3 : antiDiagonalSignGramMatrix 1 (1 : D.host.E) 0 0 = 1 := by simp [antiDiagonalSignGramMatrix]
    rw [h3, Matrix.mul_assoc] at h1
    exact h1
  rw [← hF.zB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, F.oz.isoB] at h2
  rw [negSp_gram, neg_mulVec, dotProduct_neg]
  exact congrArg Neg.neg h2

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Fib (Xo : Moduli Dw l) {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) : Over (Sp K) :=
  (Over.pullback x).obj Xo.univ.t.G

variable {Xo : Moduli Dw l} {c : Coeff l}

def Lin {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') : Prop :=
  ∀ a : 𝓞 E, (Over.pullback x).map (Xo.univ.t.act.act a) ≫ f = f ≫ (Over.pullback x').map (Xo.univ.t.act.act a)

def IsPair (N : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) : Prop :=
  IsMonHom f ∧ IsMonHom f' ∧ f ≫ f' = 𝟙 _ ^ N ∧ f' ≫ f = 𝟙 _ ^ N ∧ Lin f ∧ Lin f'

def HkWith (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) (f : Fib Xo y.x ⟶ Fib Xo z.x)
    (f' : Fib Xo z.x ⟶ Fib Xo y.x) : Prop :=
  IsPair (p ^ 2) f f' ∧ (∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j)) ∧
    IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s

def HkOver (p : ℕ) {K : Type} [Field K] [Algebra c.F K] (y z : FrPt Xo c K) : Prop :=
  AllRat Xo y.x (p ^ 2) ∧ AllRat Xo z.x (p ^ 3) ∧ ∃ f f', HkWith p y z f f'

def IsBC {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}
    (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') : Prop :=
  w = spMap φ ≫ x ∧ w' = spMap φ ≫ x' ∧
    ∀ (π : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom x)
      (π' : pullback Xo.univ.t.G.hom w' ⟶ pullback Xo.univ.t.G.hom x'),
      π ≫ pullback.fst _ _ = pullback.fst _ _ → π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      π' ≫ pullback.fst _ _ = pullback.fst _ _ → π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ →
      (g.left : pullback Xo.univ.t.G.hom w ⟶ pullback Xo.univ.t.G.hom w') ≫ π' =
        π ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')

def Ext {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') (F : G.G ⟶ G'.G) : Prop :=
  ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ ψ.left ≫ n₂.φ = m₂.φ ≫ F.left ∧
    ∀ (g : t.G.left ⟶ pullback Xo.univ.t.G.hom x) (g' : t'.G.left ⟶ pullback Xo.univ.t.G.hom x'),
      g ≫ pullback.fst _ _ = m₁.φ → g ≫ pullback.snd _ _ = t.G.hom →
      g' ≫ pullback.fst _ _ = n₁.φ → g' ≫ pullback.snd _ _ = t'.G.hom →
      g ≫ (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = ψ.left ≫ g'

def Reg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))) : Prop :=
  ∃ σ, PullbackSections.SecTie I (M ^ 2) (PullbackSections.zCast Xo.univ.t.G (PullbackSections.natCast_sq M) F) σ

def IsTransl (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ a, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (fun u => u ^ (M ^ 2) = 1) s a F

def IsPullOf (M : ℕ) {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (a : K)
    (s' : LB.Sec (PPx x')) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) ((M : ℤ) ^ 2))) (s'' : LB.Sec (PPx x')),
    IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β ∧ (∀ i, s''.f i = scal x' a i * s'.f i) ∧
      IsCarried Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) _ β s'' t

def IsTranslSum (M : ℕ) {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} (s : LB.Sec (PPx x))
    (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))) : Prop :=
  ∃ (n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk x))),
    (∀ i, IsTransl M s (F i)) ∧ ∀ j, t.f j = ∑ i, (F i).f j

end GlobalTheory.HkIntegral
end
end

