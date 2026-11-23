module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionMemPrincipalCongruenceGroup
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincTransv

theorem transv_mem_princ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 hξ h
  have hξ' : IsCMField.complexConj E ξ₀ = -ξ₀ := hξ
  have hG := h.2.2.1
  have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H Di r (-ξ₀) Gm φ0
    (by simp [cc, hξ']) h).2.2.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  set d : ℕ := (NumberField.discr E).natAbs with hd
  have hd0 : 0 < d := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  refine ⟨l.M * l.A * d, Nat.mul_pos (Nat.mul_pos hM l.A_pos) hd0, ?_⟩
  intro κ0 hκ ξ hξΛ hiso s hs hsi
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have hs' : IsCMField.complexConj E s = s := hs
  set α : E := ((l.M * l.A * d : ℕ) : E) * s * κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hs', hκc]
  have h2 : IsIntegral ℤ (2 : E) := isIntegral_natCast 2
  have hint' : ∀ v ∈ LinearMap.range φ0, IsIntegral ℤ ((d : E) * κ0 * herm Gm v ξ) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hξΛ
    have h1 := h2.mul (hint x y)
    have hdd : (d : E) = (NumberField.discr E : E) ∨ (d : E) = -(NumberField.discr E : E) := by
      rcases Int.natAbs_eq (NumberField.discr E) with h | h
      · left; rw [h, Int.cast_natCast]
      · right; rw [h, Int.cast_neg, Int.cast_natCast, neg_neg]
    have hpm : (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))) ∨
        (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          -(2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y)))) := by
      rcases hdd with e | e <;> rcases hκ with e' | e' <;> rw [e, e']
      · right; ring
      · left; ring
      · left; ring
      · right; ring
    rcases hpm with e | e <;> rw [e]
    · exact h1
    · exact h1.neg
  have key : ∀ v ∈ LinearMap.range φ0,
      (s * ((d : E) * κ0 * herm Gm v ξ)) • ξ ∈ LinearMap.range φ0 := fun v hv =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hsi.mul (hint' v hv)) hξΛ
  have e : ∀ v, (α * herm Gm v ξ) • ξ =
      (l.M * l.A) • ((s * ((d : E) * κ0 * herm Gm v ξ)) • ξ) := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  refine ⟨GlobalTheory.FlagData.transv Gm hiso α, ⟨⟨GlobalTheory.FlagData.herm_transvMat hG hiso hα, fun x => ?_⟩,
    fun a _ => ?_, fun a => ?_⟩, rfl⟩
  · change x ∈ LinearMap.range φ0 ↔ transvMat Gm ξ α *ᵥ x ∈ LinearMap.range φ0
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (by rw [e]; exact nsmul_mem (key x hx) _), fun hx => ?_⟩
    have h := nsmul_mem (key _ hx) (l.M * l.A)
    rw [← e, GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.A • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_smul]
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.M • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_comm, mul_smul]

end GlobalTheory.PrincTransv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TrivProdOfSmallExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmallExtLift

theorem triv_prod_of_small_extension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → Triv (M.pull π) → Triv M := by
  intro R _ _ ε hm A B x₀ y₀ fA fB pA pB hA hB M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have sep : IsSeparated (A ⊗ B).hom := by
    change IsSeparated (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ B).hom := by
    change Flat (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have : (A ⊗ B).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ B).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have kA : IsProper (F.obj A).hom := by
    change IsProper (pullback.snd A.hom φ); infer_instance
  have kB : IsProper (F.obj B).hom := by
    change IsProper (pullback.snd B.hom φ); infer_instance
  let i : (F.obj A ⊗ F.obj B).left ⟶ (A ⊗ B).left :=
    (Functor.Monoidal.μIso F A B).hom.left ≫ pullback.fst (A ⊗ B).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj B).hom (A ⊗ B).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ B).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A B).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A B).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A B).inv).symm
  have slice : ∀ (C : Over (Sp R)) [Flat C.hom], Function.Bijective
      (pullback.snd C.hom q).appTop.hom → ∀ (s : C ⟶ A ⊗ B) (r : A ⊗ B ⟶ C) [IsSeparated r.left],
      s ≫ r = 𝟙 C →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj C ⟶ F.obj A ⊗ F.obj B,
      sk ≫ (Functor.Monoidal.μIso F A B).hom = F.map s → _ := fun C _ hC s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ B).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst C.hom q)
      (f' := pullback.snd C.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      hC.2 hu t ht (iA := pullback.fst C.hom φ)
      (fk := pullback.snd C.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : ∀ (C D : Over (Sp R)) (z : 𝟙_ (Over (Sp R)) ⟶ D),
      toUnit (F.obj C) ≫ Functor.LaxMonoidal.ε F ≫ F.map z = F.map (toUnit C ≫ z) := fun C D z => by
    rw [F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.KuennethOne.kuenneth_injective (IsLocalRing.ResidueField R) (F.obj A)
    (F.obj B) (Functor.LaxMonoidal.ε F ≫ F.map x₀) (Functor.LaxMonoidal.ε F ≫ F.map y₀)
    inferInstance inferInstance inferInstance inferInstance
    (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom φ))
    (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom φ)) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add (f := _), gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice A _ (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom q)) _ (fst A B)
      (by change IsSeparated (pullback.fst A.hom B.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice B _ (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom q)) _ (snd A B)
      (by change IsSeparated (pullback.snd A.hom B.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ

end GlobalTheory.SmallExtLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

section Mat

variable {n : ℕ}

theorem psgn_sq (p0 k : ℕ) : psgn p0 k = 1 ∨ psgn p0 k = -1 := by
  induction k with
  | zero => left; simp [psgn]
  | succ k ih =>
    rw [psgn_succ]
    rcases ih with h | h <;> rcases sgn_sq p0 k with h' | h' <;> simp [h, h']

theorem lminor_signature (p0 : ℕ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i
      = ((psgn p0 i : ℝ) : ℂ) := by
  rw [lminor_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]
  rfl

theorem uMat_conj_eq_signature (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  have hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ) := by
    intro i
    have him : (lminor A i).im = 0 := by
      rw [hprod i]
      refine Complex.conj_eq_iff_im.1 ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)
    have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hn := h1 i
    have hp := hs i
    rw [hd, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hd, Complex.ofReal_inj]
    rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢
    · rw [abs_of_pos (by linarith)] at hn; exact hn
    · rw [abs_of_neg (by linarith)] at hn; linarith
  rw [hdiag]
  congr 1
  funext k
  have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
    rw [hprod k.succ, hprod k.castSucc]
    exact prod_castLE_succ (f := fun k => B k k) k.isLt
  rw [hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul] at hsucc
  have hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0 := by
    rcases psgn_sq p0 k with h | h <;> simp [h]
  exact (mul_left_cancel₀ hne hsucc).symm

theorem det_uMat (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (uMat_upper _)]
  simp only [uMat_diag, Finset.prod_const_one]

theorem inv_uMat_upper (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A)⁻¹.BlockTriangular id := by
  haveI := Matrix.invertibleOfIsUnitDet (uMat A) (by rw [det_uMat]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular (uMat_upper A)

theorem inv_uMat_diag (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (uMat A)⁻¹ i i = 1 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (uMat A)
    (by rw [det_uMat]; exact isUnit_one)) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, uMat_diag, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [inv_uMat_upper A h', zero_mul]
    · rw [uMat_upper A h', mul_zero]
  · simp

end Mat

theorem unit_frame_eq_orthonormal_mul_triangular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩,
    fun τ u x₀ hu => ?_⟩
  · refine ⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ),
      fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
      fun τ => ?_, fun τ i => ?_, ?_⟩
    · show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0
      rw [Matrix.det_nonsing_inv, det_uMat]
      simp
    · exact inv_uMat_upper _ hca
    · show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _
      rw [FrameDegreeData.gram_mul]
      exact uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)
    · show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1
      rw [inv_uMat_diag, norm_one]
    · funext τ
      show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]
  · intro h0
    have h2 := congrArg Matrix.det (h τ)
    rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h2
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
    rcases sgn_sq p0 k with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature, Complex.ofReal_re]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]

end GlobalTheory.UnitFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTop
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem frameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  intro K _ J m R A _ _ _ _ π X s hF A' hπ hX hs hsi hd
  obtain ⟨hdet, huniv⟩ := hF
  let ψ : R →ₐ[K] A' := π.codRestrict A' hπ
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A' := fun τ => Matrix.of fun i j => ⟨X τ i j, hX τ i j⟩
  have hg : ∀ τ, (g τ).map A'.val = X τ := fun τ => by ext i j; rfl
  let a : (A')ˣ := ⟨⟨s, hs⟩, ⟨_, hsi⟩, Subtype.ext s.mul_inv, Subtype.ext s.inv_mul⟩
  have hgu : ∀ τ, IsUnit (g τ).det := by
    intro τ
    obtain ⟨d, hdA, hd1⟩ := hd τ
    refine IsUnit.of_mul_eq_one_right (⟨d, hdA⟩ : A') ?_
    apply Subtype.ext
    have h1 : A'.val (g τ).det = (X τ).det := by
      rw [← hg τ]
      exact AlgHom.map_det A'.val (g τ)
    change d * A'.val (g τ).det = 1
    rw [h1, hd1]
  obtain ⟨k, ⟨hk1, hk2, hk3⟩, -⟩ := huniv A' ψ g a hgu
  obtain ⟨k₀, -, huq⟩ := huniv A π X s hdet
  have e1 : A'.val.comp k = k₀ := by
    apply huq
    refine ⟨?_, fun τ => ?_, ?_⟩
    · rw [AlgHom.comp_assoc, hk1]; ext t; rfl
    · rw [← hg τ, ← hk2 τ]
      conv_lhs => rw [hk2 τ, hg τ]
      ext i j; rfl
    · change A'.val (k s) = s
      rw [hk3]; rfl
  have e2 : AlgHom.id K A = k₀ := by
    apply huq
    refine ⟨by ext t; rfl, fun τ => by ext i j; rfl, rfl⟩
  rw [eq_top_iff]
  intro x _
  have : A'.val (k x) = x := by
    have := DFunLike.congr_fun (e1.trans e2.symm) x
    simpa using this
  rw [← this]
  exact (k x).2

end GlobalTheory
end

