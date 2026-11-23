module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep.Generic

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem good_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (h : m + 1 < a) (hf : Good ψ (m + 1) f) :
    Good ψ m (colT ψ (m + 1) f) := by
  refine ⟨_root_.GlobalTheory.CuspGeneric.continuous_colT_good E a ψ hψ m f hf,
    _root_.GlobalTheory.CuspGeneric.colT_isMir_invariant E a ψ hψ m f h hf,
    ?_, _root_.GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero E a ψ hψ m f h hf⟩
  intro k hk y g
  rcases Nat.lt_or_ge (m + 1) k with h1 | h1
  · exact GlobalTheory.T.columnWhittakerTransform_keeps_later_law E a ψ m f hf k h1 y g
  · obtain rfl : k = m + 1 := by omega
    exact _root_.GlobalTheory.CuspGeneric.colT_blkU_mul E a ψ hψ m f hf y g

theorem hl_of_good {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {k : ℕ} (hk : k ≤ m) (c : UnipotentBlockColumnIndex a k k → E) (g : GA E a) :
    f (ratGL E a (blkU c) * g) = f g := by
  refine hf.left _ (fun i j h => isMir_blkU c i j ?_) g
  omega

theorem colT_add (hψ : StdPsi ψ) {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ (m + 1) f) (hf' : Good ψ (m + 1) f') :
    colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := by
  funext g
  have := _root_.GlobalTheory.CuspGeneric.avg_add_of_per _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) _ _
    (per_coef hψ (eLast a (m + 1)) hf.cont (hl_of_good hf le_rfl) g)
    (per_coef hψ (eLast a (m + 1)) hf'.cont (hl_of_good hf' le_rfl) g)
  simp only [colT, coefF, mul_add]
  exact this

theorem colT_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) :
    colT ψ (m + 1) (fun g => c * f g) = fun g => c * colT ψ (m + 1) f g := by
  funext g
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  ring

theorem whit_good (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f →
    Good ψ 0 (whit ψ m f) ∧ (f ≠ 0 → whit ψ m f ≠ 0) := by
  induction m with
  | zero => exact fun _ f hf => ⟨hf, id⟩
  | succ m ih =>
    intro h f hf
    have h1 : m + 1 < a := by omega
    obtain ⟨h2, h3⟩ := ih (Or.inl (by omega)) (good_colT hψ h1 hf)
    exact ⟨h2, fun h0 => h3 (_root_.GlobalTheory.CuspGeneric.colT_ne_zero_of_good E a ψ hψ m f h1 hf h0)⟩

theorem whit_add (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Good ψ m f → Good ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have h1 : m + 1 < a := by omega
    rw [whit_succ, whit_succ, whit_succ, colT_add hψ hf hf']
    exact ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf')

theorem whit_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) : whit ψ m (fun g => c * f g) = fun g => c * whit ψ m f g := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [whit_succ, whit_succ, colT_smul, ih]

theorem whit_rt (m : ℕ) (f : GA E a → ℂ) (h g : GA E a) : whit ψ m (fun x => f (x * h)) g = whit ψ m f (g * h) := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    rw [whit_succ, whit_succ, ← ih]
    congr 1
    funext x
    simp only [colT, coefF, mul_assoc]

def locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) Circle where
  toFun y := ⟨ψ (sFin E (sLoc E w y)), by simpa [Submonoid.unitSphere] using hψ.norm _⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' x y := by
    apply Circle.ext
    change ψ (sFin E (sLoc E w (x + y))) = ψ (sFin E (sLoc E w x)) * ψ (sFin E (sLoc E w y))
    rw [map_add (f := _), map_add (f := _), AddChar.map_add_eq_mul]

theorem coe_locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    (locPsi hψ w y : ℂ) = ψ (sFin E (sLoc E w y)) := rfl


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem isGeneric_of_isLocComp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    GlobalTheory.LocGL.IsGeneric σ.ρ := by
  rintro E _ _ _ a P w σ ⟨f, hf0, hf⟩
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CuspGeneric.exists_stdPsi E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := _root_.GlobalTheory.CuspGeneric.exists_split_loc E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end GlobalTheory.CuspRep.Generic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlockDiagReductionToFlagGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section
namespace GlobalTheory.LiftDiag

section Mat
variable {k : Type} [CommRing k] {n r t : ℕ}

theorem rowIx_inl (h : r + t = n) (j : Fin r) : ((rowIx h) (Sum.inl j)).val = j.val := by
  simp [rowIx]

theorem symm_lower (h : r + t = n) {a : Fin n} (ha : r ≤ a.val) : ∃ j, (rowIx h).symm a = Sum.inr j := by
  rcases hx : (rowIx h).symm a with j | j
  · exfalso
    have : a = rowIx h (Sum.inl j) := by rw [← hx, Equiv.apply_symm_apply]
    have h2 := rowIx_inl h j
    rw [← this] at h2
    omega
  · exact ⟨j, rfl⟩

theorem symm_castLE (h : r + t = n) (hr : r ≤ n) (a : Fin r) : (rowIx h).symm (Fin.castLE hr a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  ext
  rw [rowIx_inl]
  rfl

theorem lower_row (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {a : Fin n} (ha : r ≤ a.val) (b : Fin n) :
    ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b := by
  obtain ⟨j, hj⟩ := symm_lower h ha
  rw [Matrix.submatrix_apply, hj]
  have e1 : (1 : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) ((rowIx h).symm a) ((rowIx h).symm b) := by
    simp only [Matrix.one_apply, (rowIx h).symm.injective.eq_iff]
  rw [e1, hj]
  rcases (rowIx h).symm b with j' | j'
  · simp [Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
  · simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem mem_blockTri_diag (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    g ∈ blockTri b := by
  intro i j hij
  have hi : r ≤ i.val := by
    by_contra hc
    rw [hb i (by omega)] at hij
    omega
  show (g : Matrix (Fin n) (Fin n) k) i j = 0
  rw [hg, lower_row h A hi, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem blockDiagonalPart_blockDiagOne_reindexed_eq_one (h : r + t = n) (A : Matrix (Fin r) (Fin r) k) {b : Fin n → ℕ}
    (hb : ∀ a : Fin n, a.val < r → b a = 0) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm)
    {c : ℕ} (hc : c ≠ 0) : dBlk b c g = 1 := by
  apply Units.ext
  rw [diag_block_det_val c (mem_blockTri_diag h A hb g hg), Units.val_one]
  have : (g : Matrix (Fin n) (Fin n) k).submatrix (Subtype.val : {a : Fin n // b a = c} → Fin n) (Subtype.val : {a : Fin n // b a = c} → Fin n) = 1 := by
    ext x y
    have hx : r ≤ x.1.val := by
      by_contra hh
      exact hc (x.2.symm.trans (hb _ (by omega)))
    rw [Matrix.submatrix_apply, hg, lower_row h A hx]
    simp only [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem topLeftBlock_blockDiagOne_reindexed_eq (h : r + t = n) (hr : r ≤ n) (A : Matrix (Fin r) (Fin r) k) (g : GL (Fin n) k)
    (hg : (g : Matrix (Fin n) (Fin n) k) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) k)).submatrix (rowIx h).symm (rowIx h).symm) :
    ((upperLeftBlock hr g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = A := by
  have hb : ∀ a : Fin n, a.val < r → blk2 r a = 0 := fun a ha => by simp [blk2, ha]
  rw [upper_block_val_submatrix hr (mem_blockTri_diag h A hb g hg), hg]
  ext a b
  simp only [Matrix.submatrix_apply, symm_castLE h hr, Matrix.fromBlocks_apply₁₁]

theorem blockIndexSecond_eq_zero_of_lt (r : ℕ) (a : Fin n) (ha : a.val < r) : blk2 r a = 0 := by simp [blk2, ha]

theorem blkOf_low (r t : ℕ) (a : Fin n) (ha : a.val < r) : blkOf r t a = 0 := by simp [blkOf, ha]

end Mat

end GlobalTheory.LiftDiag

namespace GlobalTheory.LiftDiag

theorem lift_diag : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (g : G), (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) → ∀ κ : GA D (Vc D i), κ ∈ GfC (Vc D i) → finE (Vc D i) κ ∈ Formalism.L2.DIV.St (R.βV i) → ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) = (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → (∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → PP' ≠ PP → redFn (R.βV i) PP' (finE (Vc D i) κ) = 1) → IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t PP hPP g hg κ hκ hSt hN hoth
  have memb : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → redFn (R.βV i) PP' (finE (Vc D i) κ) ∈ blockTri b := by
    intro b hb PP' hP'
    by_cases he : PP' = PP
    · subst he; exact mem_blockTri_diag (rank_V i) _ hb _ hN
    · rw [hoth PP' hP' he]; exact Subgroup.one_mem _
  have dB : ∀ b : Fin (Vc D i).rank → ℕ, (∀ a : Fin (Vc D i).rank, a.val < D.R.r → b a = 0) → ∀ c : ℕ, c ≠ 0 →
      ∀ PP', PP' ∈ R.Pg ∨ PP' ∈ R.Q t → dBlk b c (redFn (R.βV i) PP' (finE (Vc D i) κ)) = 1 := by
    intro b hb c hc PP' hP'
    by_cases he : PP' = PP
    · subst he; exact blockDiagonalPart_blockDiagOne_reindexed_eq_one (rank_V i) _ hb _ hN hc
    · rw [hoth PP' hP' he]; exact blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨hκ, ?_, ?_⟩, ?_⟩
  · exact mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, hSt,
      fun PP' hP' => memb _ (blkOf_low _ _) PP' (Or.inl hP'), fun PP' hP' => memb _ (blockIndexSecond_eq_zero_of_lt _) PP' (Or.inr hP')⟩
  · funext PP'
    obtain ⟨PP', hP'⟩ := PP'
    show upperLeftBlock _ (redFn (R.βV i) PP' (finE (Vc D i) κ)) = R.eG g ⟨PP', hP'⟩
    by_cases he : PP' = PP
    · subst he; apply Units.ext; exact topLeftBlock_blockDiagOne_reindexed_eq (rank_V i) _ _ _ hN
    · rw [hoth PP' (Or.inl hP') he]
      have h1 : upperLeftBlock (r_le_V i) (1 : GL (Fin (Vc D i).rank) (kP PP')) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      have h2 : R.eG g ⟨PP', hP'⟩ = 1 := hg ⟨PP', hP'⟩ (fun h => he (congrArg Subtype.val h))
      rw [h2]
      exact h1
  · have key : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = 1 := by
      unfold levFn
      rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
      · exact (extendOne_of_mem _ (Subgroup.mem_top _)).trans rfl
      · intro PP' hP'
        exact (congrArg _ (dB _ (blockIndexSecond_eq_zero_of_lt _) 1 one_ne_zero PP' (Or.inr hP'))).trans (map_one _)
      · intro PP' hP'
        exact Finset.prod_eq_one fun c _ =>
          (congrArg _ (dB _ (blkOf_low _ _) (c + 1) (Nat.succ_ne_zero c) PP' (Or.inl hP'))).trans (map_one _)
    show ((levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) : ℂˣ) : ℂ) = 1
    rw [key, Units.val_one]

end GlobalTheory.LiftDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := _root_.GlobalTheory.TameCoeff.main l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (_root_.GlobalTheory.TameCoeff.main l a e he hnd LL').2 hUnr
  refine _root_.GlobalTheory.BaseCoef.thmT_descend l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := _root_.GlobalTheory.GoodLatt.main hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := _root_.GlobalTheory.TheoremT.liftF_of_isGood hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := _root_.GlobalTheory.BK.maxPeriod_bounds l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.ThetaPull

noncomputable section

namespace GlobalTheory.ConjPairLoc

theorem irred_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (φ : G →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (MonoidHom.comp ρ φ) := by
  let e : Subrepresentation (MonoidHom.comp ρ φ : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact W.apply_mem_toSubmodule g hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) (g : G) (x : V) :
    e.toLinearEquiv (ρ g x) = τ g (e.toLinearEquiv x) :=
  LinearMap.congr_fun (e.isIntertwining' g) x

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {k k' : GL (Fin a) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin a) (v.adicCompletion E) => g.val i j) (h v)

theorem conjFin_locGL (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) ((conjSrc c v).adicCompletion E)) :
    GeneralLinearGroup.map (conjFin c) (locGL E a _ g) = locGL E a v (GeneralLinearGroup.map (conjLoc c v) g) := by
  refine gl_ext fun u => ?_
  have e : GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (conjFin c) (locGL E a _ g)) =
      GeneralLinearGroup.map (conjLoc c u) (GeneralLinearGroup.map (pLoc E (conjSrc c u)) (locGL E a _ g)) := by
    ext i j
    rfl
  rw [e]
  by_cases h : u = v
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective c e)), map_one]

theorem map_conjLoc_surjective [IsCMField E] (v : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin a) (conjLoc (IsCMField.complexConj E).toRingEquiv v)) := by
  intro g
  refine ⟨GeneralLinearGroup.map (pLoc E _) (GeneralLinearGroup.map (cFin E) (locGL E a v g)), ?_⟩
  conv_rhs => rw [← pLoc_locGL v g]
  ext i j : 2
  exact congrArg (pLoc E v) (cFin_cFin _)

end GlobalTheory.ConjPairLoc

end
end

