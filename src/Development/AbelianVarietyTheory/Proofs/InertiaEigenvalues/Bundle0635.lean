module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7} (W : HSp D)

theorem exists_gqMat (γ : GQ W) : ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat c = mt W γ :=
  mem_ratMx.1 ((mem_GQ_iff W γ).1 γ.2)

def gqMat (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_gqMat W γ)

theorem rat_gqMat (γ : GQ W) : rat (gqMat W γ) = mt W γ := Classical.choose_spec (exists_gqMat W γ)

theorem gqMat_map (γ : GQ W) : (gqMat W γ).map (incA D) = mt W γ := rat_gqMat W γ

theorem gqMat_mul (γ δ : GQ W) : gqMat W (γ * δ) = gqMat W γ * gqMat W δ :=
  rat_injective (by rw [rat_mul, rat_gqMat, rat_gqMat, rat_gqMat]; rfl)

theorem gqMat_one : gqMat W 1 = 1 := rat_injective (by rw [rat_gqMat, rat_one]; rfl)

theorem gqMat_inv_mul (γ : GQ W) : gqMat W γ⁻¹ * gqMat W γ = 1 := by
  rw [← gqMat_mul, inv_mul_cancel, gqMat_one]

theorem gqMat_mul_inv (γ : GQ W) : gqMat W γ * gqMat W γ⁻¹ = 1 := by
  rw [← gqMat_mul, mul_inv_cancel, gqMat_one]

theorem gqMat_unitary (γ : GQ W) : (gqMat W γ)ᴴ * W.gram * gqMat W γ = W.gram := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_gqMat]
  exact mt_rel W γ

def actEquiv (γ : GQ W) :
    ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E] ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearEquiv.prodCongr
    (LinearEquiv.ofLinear (Matrix.toLin' (gqMat W γ)) (Matrix.toLin' (gqMat W γ⁻¹))
      (by rw [← Matrix.toLin'_mul, gqMat_mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, gqMat_inv_mul, Matrix.toLin'_one]))
    (LinearEquiv.refl _ _)

theorem actEquiv_apply (γ : GQ W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    actEquiv W γ y = (gqMat W γ *ᵥ y.1, y.2) := rfl

theorem isotropic_mulVec (γ : GQ W) (x x' : Fin W.rank → D.host.E) :
    star (gqMat W γ *ᵥ x) ⬝ᵥ W.gram *ᵥ (gqMat W γ *ᵥ x') = star x ⬝ᵥ W.gram *ᵥ x' := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, gqMat_unitary]

def lagAct (γ : GQ W) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _), by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [LinearEquiv.coe_coe, actEquiv_apply]
    rw [isotropic_mulVec]
    exact Y.2.2 y hy y' hy'⟩

theorem mem_lagAct (γ : GQ W) (Y : Lag W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    y ∈ (lagAct W γ Y).1 ↔ (gqMat W γ⁻¹ *ᵥ y.1, y.2) ∈ Y.1 := by
  show y ∈ Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem lagAct_one (Y : Lag W) : lagAct W 1 Y = Y := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, inv_one, gqMat_one, Matrix.one_mulVec]

theorem lagAct_mul (γ δ : GQ W) (Y : Lag W) : lagAct W (γ * δ) Y = lagAct W γ (lagAct W δ Y) := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, mem_lagAct, mem_lagAct, _root_.mul_inv_rev, gqMat_mul]
  simp only [Matrix.mulVec_mulVec]

theorem isLagFrame_lagAct (γ : GQ W) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    IsLagFrame W (lagAct W γ Y) (gqMat W γ * C.1, C.2) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (actEquiv W γ).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

abbrev NGLag (W : HSp D) : Type := {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}

theorem lagAct_ne_bot (γ : GQ W) (Y : Lag W) (h : Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥) :
    (lagAct W γ Y).1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 h
  refine (Submodule.ne_bot_iff _).2 ⟨gqMat W γ *ᵥ x, ?_, ?_⟩
  · rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lagAct, Matrix.mulVec_mulVec, gqMat_inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h0
    apply hx0
    have := congrArg (fun v => gqMat W γ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, gqMat_inv_mul] using this

def ngAct (γ : GQ W) (Y : NGLag W) : NGLag W := ⟨lagAct W γ Y.1, lagAct_ne_bot W γ Y.1 Y.2⟩

theorem ngAct_one (Y : NGLag W) : ngAct W 1 Y = Y := Subtype.ext (lagAct_one W Y.1)

theorem ngAct_mul (γ δ : GQ W) (Y : NGLag W) : ngAct W (γ * δ) Y = ngAct W γ (ngAct W δ Y) :=
  Subtype.ext (lagAct_mul W γ δ Y.1)

end GlobalTheory.RallisCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open Matrix

namespace GlobalTheory.IwasawaAdelic

theorem cornerGL_entry {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j
      = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_entry_ne {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_entry]; simp [Matrix.one_apply_ne h]

theorem cornerGL_entry_same {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i : Fin a) :
    (cornerGL a s g).val i i = 1 - s 1 + s (g.val i i) := by
  rw [cornerGL_entry]; simp

theorem stdBlocks_lt_of_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s}
    (i : Fin (d a)) (j : Fin (d b)) (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_parab_of_upper {R : Type} [CommRing R] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (b : GL (Fin N) R) (hb : (b : Matrix (Fin N) (Fin N) R).BlockTriangular id) :
    b ∈ parab R (stdBlocks n h) := by
  rw [mem_parab_iff]
  intro a a' i j hlt
  exact hb (stdBlocks_lt_of_lt n h i j hlt)

theorem exists_upper_mul_unitary (N : ℕ) (y : GL (Fin N) ℂ) :
    ∃ b : GL (Fin N) ℂ, (b : Matrix (Fin N) (Fin N) ℂ).BlockTriangular id ∧
      ∃ k : Matrix (Fin N) (Fin N) ℂ, k ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
        (y : Matrix (Fin N) (Fin N) ℂ) = b * k := by
  set A : Matrix (Fin N) (Fin N) ℂ := ((y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hAdef
  have hyA : (y : Matrix (Fin N) (Fin N) ℂ) * A = 1 := by simp [hAdef]
  have hAdet : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (y⁻¹).isUnit
  have hdet : IsUnit (Aᴴ * A).det := by
    rw [det_mul, det_conjTranspose]; exact hAdet.star.mul hAdet
  obtain ⟨Q, u, hQ, hu, hudet, hA⟩ := GlobalTheory.QRDecomp.exists_qr N N A hdet
  letI := u.invertibleOfIsUnitDet hudet
  refine ⟨(Matrix.nonsingInvUnit u hudet)⁻¹, ?_, Qᴴ, ?_, ?_⟩
  · show (u⁻¹).BlockTriangular id
    exact Matrix.blockTriangular_inv_of_blockTriangular hu
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 hQ
  · show (y : Matrix (Fin N) (Fin N) ℂ) = u⁻¹ * Qᴴ
    have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.1 hQ
    have h1 : (Q * u) * (u⁻¹ * Qᴴ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u, Matrix.mul_nonsing_inv u hudet, Matrix.one_mul, hQQ]
    calc (y : Matrix (Fin N) (Fin N) ℂ) = (y : Matrix (Fin N) (Fin N) ℂ) * ((Q * u) * (u⁻¹ * Qᴴ)) := by
          rw [h1, Matrix.mul_one]
      _ = u⁻¹ * Qᴴ := by rw [← Matrix.mul_assoc, ← hA, hyA, Matrix.one_mul]

theorem ext_eval {ι : Type} {N : ℕ} {P Q : Matrix (Fin N) (Fin N) (ι → ℂ)}
    (hPQ : ∀ v, P.map (Pi.evalRingHom (fun _ : ι => ℂ) v) = Q.map (Pi.evalRingHom (fun _ : ι => ℂ) v)) :
    P = Q := by
  ext i j v; exact congrFun (congrFun (hPQ v) i) j

theorem exists_upper_mul_unitary_inf (E : Type) [Field E] (N : ℕ) (y : GL (Fin N) (Cinf E)) :
    ∃ b : GL (Fin N) (Cinf E), (b : Matrix (Fin N) (Fin N) (Cinf E)).BlockTriangular id ∧
      ∃ k : Kinf E N, y = b * Unitary.toUnits k := by
  let ev : InfinitePlace E → (Cinf E →+* ℂ) := fun v => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v
  choose B hB K hK hyK using fun v => exists_upper_mul_unitary N (Matrix.GeneralLinearGroup.map (ev v) y)
  let bm : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (B v : Matrix (Fin N) (Fin N) ℂ) i j
  let bi : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j
  let km : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => K v i j
  have hbm : ∀ v, bm.map (ev v) = (B v : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hbi : ∀ v, bi.map (ev v) = (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hkm : ∀ v, km.map (ev v) = K v := fun v => rfl
  have h1 : bm * bi = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have h2 : bi * bm = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have hkU : km ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    refine ext_eval fun v => ?_
    have hs : (star km).map (ev v) = star (K v) := by
      ext i j; rfl
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hs, hkm]
    exact (Matrix.mem_unitaryGroup_iff').1 (hK v)
  refine ⟨⟨bm, bi, h1, h2⟩, ?_, ⟨km, hkU⟩, ?_⟩
  · intro i j hij
    funext v
    exact hB v hij
  · apply Units.ext
    refine ext_eval fun v => ?_
    show (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev v) = (bm * km).map (ev v)
    rw [Matrix.map_mul, hbm, hkm]
    exact hyK v

theorem infGL_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    infGL E N = cornerGL N (GlobalTheory.CuspRep.sInf E) := rfl

theorem infGL_mem_unipRad (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (u : GL (Fin N) (Cinf E))
    (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) : infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [infGL_eq, cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [infGL_eq, cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

theorem infGL_leviEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (l : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) l)
      = leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (l i)) := by
  have leviEmb_apply_same : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) a i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨a, j⟩) = (l a : Matrix _ _ R) i j := by
    intro R _ l a i j
    simp [leviEmb, blockDiagonal'_apply_eq]
  have leviEmb_apply_ne : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) {a b}, a ≠ b → ∀ i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = 0 := by
    intro R _ l a b hab i j
    simp [leviEmb, blockDiagonal'_apply, hab]
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [infGL_eq, infGL_eq, cornerGL_entry_same, cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, infGL_eq, cornerGL_entry_ne _ _ hne, cornerGL_entry_ne _ _ hij, leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ hab, infGL_eq, cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ hab, map_zero]

theorem iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  intro E _ _ _ c N n h x
  obtain ⟨b, hb, k, hy⟩ := exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  let p : parab (Cinf E) (stdBlocks n h) := ⟨b, mem_parab_of_upper n h b hb⟩
  let l := leviProj (Cinf E) (stdBlocks n h) p
  have hLp : leviEmb (Cinf E) (stdBlocks n h) l ∈ parab (Cinf E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, blockDiagonal'_apply, hab.ne']
  let Lp : parab (Cinf E) (stdBlocks n h) := ⟨leviEmb (Cinf E) (stdBlocks n h) l, hLp⟩
  have hproj : leviProj (Cinf E) (stdBlocks n h) Lp = l := by
    funext a
    ext i j
    simp [leviProj_apply, Lp, leviEmb, blockDiagonal'_apply_eq]
  let u : GL (Fin N) (Cinf E) := ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
  have hu : u ∈ unipRad (Cinf E) (stdBlocks n h) := by
    apply (coe_mem_unipRad (Cinf E) (Lp⁻¹ * p)).2
    simp [hproj, l]
  have hbu : b = leviEmb (Cinf E) (stdBlocks n h) l * u := by
    change (p : GL (Fin N) (Cinf E)) = (Lp : GL (Fin N) (Cinf E)) * ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
    simp
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩) with hL
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := by
    let U : parab (Cinf E) (stdBlocks n h) := ⟨u, (mem_unipRad.1 hu).1⟩
    have hU : leviProj (Cinf E) (stdBlocks n h) U = 1 := (coe_mem_unipRad (Cinf E) U).1 hu
    change ((Lp * U * Lp⁻¹ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)) ∈ _
    rw [coe_mem_unipRad, map_mul, map_mul, map_inv, hU, mul_one, mul_inv_cancel]
  refine ⟨infGL E N (L * u * L⁻¹), infGL_mem_unipRad E n h _ hu', fun i => infGL E (n i) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩ i), k, Matrix.GeneralLinearGroup.map (pFin E) x, ?_⟩
  rw [← infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  rw [hbu]
  simp only [map_mul, map_inv]
  group

end GlobalTheory.IwasawaAdelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.AdjUp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) : GA D (Vc D i) → (R.cV i).W :=
  fun h => ∑ k, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h • b k

theorem val_zero (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    val R i v 0 = 0 := by
  funext g
  simp [val]

theorem upLift_zero {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (h : GA D V) : upLift om ν 𝓖 f 0 h = 0 := by
  simp [upLift]

end GlobalTheory.AdjUp

end

namespace GlobalTheory.AdjUp

theorem adjoint_formula_of_kernel {H₁ H₂ W Gv Gw : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [FiniteDimensional ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace Gv] [MeasurableSpace Gw]
    (th : H₁ →ₗ[ℂ] H₂) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ W) (μW : Measure Gw) (μV : Measure Gv)
    (φ : H₂ → Gw → ℂ) (ψ : H₁ → Gw → ℂ) (ext : H₁ →ₗ[ℂ] (Gv → W)) (K : Fin n → H₂ → Gv → ℂ) (P c : ℝ)
    (hP0 : 0 ≤ P) (hc : 0 < c)
    (hPW : ∀ y z, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g, star (φ y g) * φ z g ∂μW)
    (hφ : ∀ u, φ (th u) = ψ u) (hφ0 : φ 0 = 0) (hK0 : ∀ k h, K k 0 h = 0)
    (hcV : ∀ u u', ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h, ⟪ext u h, ext u' h⟫_ℂ ∂μV ∧
      ∀ a a' : W, Integrable (fun h => star ⟪a, ext u h⟫_ℂ * ⟪a', ext u' h⟫_ℂ) μV)
    (h3 : ∀ y u, ∫ g, star (φ y g) * ψ u g ∂μW = ∫ h, ⟪∑ k, K k y h • b k, ext u h⟫_ℂ ∂μV)
    (h4 : ∀ y, ∃ u, ext u = fun h => ∑ k, K k y h • b k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
  choose U hU using h4
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hcoord : ∀ y k h, ⟪b k, ext (U y) h⟫_ℂ = K k y h := fun y k h => by
    rw [hU y]; exact b.orthonormal.inner_right_fintype _ k
  have hadj : ∀ y u, ⟪LinearMap.adjoint th y, u⟫_ℂ = (((P / c : ℝ)) : ℂ) * ⟪U y, u⟫_ℂ := by
    intro y u
    rw [LinearMap.adjoint_inner_left, hPW, hφ, h3, (hcV (U y) u).1, hU y, Complex.ofReal_div]
    field_simp
  have hsum : ∀ x y h, ⟪ext (U x) h, ext (U y) h⟫_ℂ = ∑ k, star (K k x h) * K k y h := by
    intro x y h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord, ← hcoord, ← inner_conj_symm]
    rfl
  by_cases hzero : P = 0
  · refine ⟨1, one_pos, fun x y => ?_⟩
    have h0 : ∀ z : H₂, z = 0 := fun z => by
      have := hPW z z
      rw [hzero, Complex.ofReal_zero, zero_mul] at this
      exact inner_self_eq_zero.1 this
    rw [h0 x, h0 y, map_zero, inner_zero_left]
    simp [hK0]
  · have hpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hzero)
    refine ⟨P ^ 2 / c, by positivity, fun x y => ?_⟩
    have hint : ∀ k ∈ Finset.univ, Integrable (fun h => star (K k x h) * K k y h) μV := by
      intro k _
      have := (hcV (U x) (U y)).2 (b k) (b k)
      simpa only [hcoord] using this
    have e1 : ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
        (((P / c : ℝ)) : ℂ) * (((P / c : ℝ)) : ℂ) * ⟪U x, U y⟫_ℂ := by
      rw [hadj x, ← inner_conj_symm, hadj y, map_mul, Complex.conj_ofReal, inner_conj_symm, mul_assoc]
    have e2 : ⟪U x, U y⟫_ℂ = (c : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
      rw [(hcV (U x) (U y)).1, ← integral_finsetSum _ hint]
      simp only [hsum]
    rw [e1, e2]
    push_cast
    field_simp

end GlobalTheory.AdjUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | exact GlobalTheory.BKAtQD.admBK_embeddingTypeJumps | (intros; apply GlobalTheory.BKAtQD.admBK_embeddingTypeJumps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalFil

theorem ENStable_and_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH
  have h1 := _root_.GlobalTheory.NgalENM.EN_mem_Man hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH
  exact ⟨h1, _root_.GlobalTheory.JumpsOfM.main hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH h1⟩

end GlobalTheory.NgalFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteHeightBreuilKisinLatticeSemistableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteHeight_breuilKisin_lattice_semistable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (b : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), IsUnit (Y.map (inclW l)) ∧ IsUnit Z ∧ (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) ∧ A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Y.map WittVector.frobenius = Y * A.map bk.ev := by
  first | exact @GlobalTheory.BKLim.WHeight.exists_height | exact GlobalTheory.BKLim.WHeight.exists_height | (intros; apply GlobalTheory.BKLim.WHeight.exists_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelFormsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  first | exact @GlobalTheory.UnitaryBC.finiteDimensional_levelForms | exact GlobalTheory.UnitaryBC.finiteDimensional_levelForms | (intros; apply GlobalTheory.UnitaryBC.finiteDimensional_levelForms <;> assumption)
end

