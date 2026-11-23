module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Formalism.LocalRingCardinality.DataDIV

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)
open GlobalTheory.Cartier (IsRegularFn IsRegularSec SecMaps germ_resG ext_germK)
open GlobalTheory.VB (IsVB IsFrame IsSubbundle Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.Vert

open Formalism.BasicNotions.DV (ITh FPair)

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def ramIdx (p : ℕ) : ℕ := (IsDiscreteValuationRing.addVal O p).toNat

section Char

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem natCast_ne_zero : (p : O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero


omit [Fact p.Prime] [CharZero O] in
theorem natCast_mem_maximalIdeal : (p : O) ∈ maximalIdeal O :=
  (residue_eq_zero_iff _).1 ((map_natCast _ p).trans (CharP.cast_eq_zero _ p))


omit [CharP (ResidueField O) p] in
theorem natCast_ramIdx : (ramIdx O p : ℕ∞) = IsDiscreteValuationRing.addVal O p :=
  ENat.natCast_toNat (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (natCast_ne_zero O p))

theorem ramIdx_ne_zero : ramIdx O p ≠ 0 := fun h =>
  natCast_mem_maximalIdeal O p (IsDiscreteValuationRing.addVal_eq_zero_iff.1
    ((natCast_ramIdx O p).symm.trans (by rw [h]; rfl)))

end Char

theorem charP_residueField_padicInt (p : ℕ) [Fact p.Prime] : CharP (ResidueField ℤ_[p]) p :=
  charP_of_injective_ringHom (f := PadicInt.residueField.symm.toRingHom)
    PadicInt.residueField.symm.injective p

namespace Model

variable {O} (Z : Model O)

theorem exists_isPullback_gen (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] :
    ∃ q : Z.gen.toScheme ⟶ Sp K, IsPullback Z.gen.ι q Z.str (spMap (algebraMap O K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away ϖ K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (.powers ϖ) (nonZeroDivisors O)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨_, ⟨n, rfl⟩, hn.dvd⟩
  have : IsOpenImmersion (spMap (algebraMap O K)) := .of_isLocalization ϖ
  have h : Z.str ⁻¹ᵁ (spMap (algebraMap O K)).opensRange = Z.gen.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Z.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit]
    ext x
    refine Iff.trans ?_ mem_basicOpen_const.symm
    exact (Set.ext_iff.1 (PrimeSpectrum.localization_away_comap_range K ϖ) _)
  have h' : Set.range (Z.gen.ι ≫ Z.str) ⊆ Set.range (spMap (algebraMap O K)) := by
    rintro _ ⟨x, rfl⟩
    exact h.ge ⟨x, rfl⟩
  exact ⟨_, (IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ h').symm h).flip⟩

abbrev VDivQ : Type := ℚ ⊗[ℤ] Z.VDivZ


variable {Z} in
def toQ : Z.VDivZ →+ Z.VDivQ := (TensorProduct.mk ℤ ℚ Z.VDivZ 1).toAddMonoidHom

def cDQ : Z.VDivQ →ₗ[ℚ] PicSym Z.X :=
  LinearMap.liftBaseChange ℚ (firstChernPic.comp Z.vCls).toIntLinearMap

def vDegQ : Z.VDivQ →ₗ[ℚ] PicSym Z.X →ₗ[ℚ] ℚ := LinearMap.liftBaseChange ℚ Z.vDeg.toIntLinearMap

def capDeg_vp (p : ℕ) : Z.VDivQ →ₗ[ℚ] PicSym Z.X →ₗ[ℚ] ℚ := (ramIdx O p : ℚ)⁻¹ • Z.vDegQ

variable {Z}

@[simp] theorem cDQ_toQ (D : Z.VDivZ) : Z.cDQ (toQ D) = firstChernPic (Z.vCls D) := by
  simp [cDQ, toQ]

@[simp] theorem vDegQ_toQ (D : Z.VDivZ) : Z.vDegQ (toQ D) = Z.vDeg D := by
  simp [vDegQ, toQ]

theorem capDeg_vp_toQ (p : ℕ) (D : Z.VDivZ) (Q : PicSym Z.X) :
    Z.capDeg_vp p (toQ D) Q = Z.vDeg D Q / ramIdx O p := by
  simp [capDeg_vp, div_eq_inv_mul]

section Theory

variable (Z) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def divP : Z.VDivZ := Z.div p (natCast_ne_zero O p)



set_option linter.overlappingInstances false in
@[reducible] def toITh [CharP (ResidueField O) p] : ITh where
  LB := SmallPic Z.X
  Ch := PicSym Z.X
  c1 := symOf
  VDiv := Z.VDivQ
  cD := Z.cDQ
  capDeg := Z.capDeg_vp p
  divP := toQ (Z.divP p)
  cD_divP := by simp [divP]
  dim := Z.relDim + 1

variable {Z}

theorem toITh_capDeg_eq_zero (D : Z.VDivQ) {n : ℕ} (hn : n ≠ Z.relDim) {x : PicSym Z.X}
    (hx : x ∈ symDeg (SmallPic Z.X) n) : (Z.toITh p).capDeg D x = 0 := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D => simp [capDeg_vp, vDegQ, vDeg_eq_zero D hn hx]
  | add a b ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]

variable {E E' : Z.X.Modules} {N : ℕ} {φ : Z.GenIso E E'}

def FlagPair.toFPair (P : FlagPair φ N) : FPair (Z.toITh p) N where
  x i := smallCls _ (P.fl.isLB_root i)
  x' i := smallCls _ (P.fl'.isLB_root i)
  Dv i := toQ (P.div i).cls
  hx i := by
    change firstChernPic (cls _ _) = firstChernPic (cls _ _) - Z.cDQ _
    rw [P.cls_root', map_sub, cDQ_toQ]

theorem FlagPair.toFPair_ofSMul_Dv (fl : Flag E N) (i : Fin N) :
    ((FlagPair.ofSMul fl p (natCast_ne_zero O p)).toFPair p).Dv i = (Z.toITh p).divP :=
  congrArg toQ (FlagPair.cls_div_ofSMul fl _ _ i)

end Theory


variable (O) in
def base : Model O where
  X := Sp O
  str := 𝟙 _
  isProjOver := Models.Point.isProjOver_id O

@[simp] theorem relDim_base : (base O).relDim = 0 :=
  relDim_eq_iff.2 ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := O)).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one O))


variable (Z) in
def toBase : Hom Z (base O) where
  f := Z.str
  comp_str := Category.comp_id _
  surjective := ⟨fun y => Set.mem_range.1 (((PrimeSpectrum.le_iff_specializes _ y).1
    ((mem_gen_iff_eq_bot.1 Z.genericPoint_mem_gen).trans_le bot_le)).mem_closed
      Z.str.isClosedMap.isClosed_range ⟨_, rfl⟩)⟩

@[simp] theorem relDim_toBase : Z.toBase.relDim = Z.relDim := by simp [Hom.relDim]

theorem chiLen_twist_effConst {g : O} (hg : g ≠ 0) {M : LB Z.X} (hM : M.IsLB)
    (h : ∀ n, 0 < n → Subsingleton (coh (twist (structureModule Z.X) M) n))
    [Module.Free O (coh (twist (structureModule Z.X) M) 0)] :
    chiLen O (twist (divMod (Z.effConst g hg).1) M) = (IsDiscreteValuationRing.addVal O g).toNat *
      Module.finrank O (coh (twist (structureModule Z.X) M) 0) := by
  have := Twist.isFiniteQC_twist (F := structureModule Z.X) hM
  have := finite_coh_of_isProjOver Z.const_eq (twist (structureModule Z.X) M) Z.isProjOver 0
  obtain ⟨e⟩ := nonempty_cokernel_iso (.principal (Z.const g) (Z.isRegularFn_const hg))
    (φ := smulHom (structureModule Z.X) (Z.const g)) fun _ _ _ => ⟨.refl _ _, fun _ => rfl⟩
  have : Mono (smulHom (structureModule Z.X) (Z.const g)) :=
    mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun _ _ h =>
      (mul_cancel_left_mem_nonZeroDivisors (Z.isRegularFn_const hg W le_top)).1 h⟩
  have hS := Twist.shortExact_map hM (S := .mk _ (cokernel.π _)
    (cokernel.condition (smulHom (structureModule Z.X) (Z.const g))))
    { exact := ShortComplex.exact_cokernel _ }
  have hf : Twist.map M (smulHom (structureModule Z.X) (Z.const g)) = smulHom _ (Z.const g) :=
    Twist.hom_ext fun V s i => by
      rw [Twist.coord_map_app, smulHom_app_apply, smulHom_app_apply, Twist.coord_smul]
      exact congrArg (· • Twist.coord s i) (map_restrictGlobal (homOfLE inf_le_left) _).symm
  refine (chiLen_congr O ((twistFunctor M).mapIso e)).symm.trans ?_
  refine (chiLen_eq_sum_range O 1 fun n hn =>
    cohOn.subsingleton₃ hS ⊤ n (h n hn) (h (n + 1) n.succ_pos)).trans ?_
  have e' := ((cohOn.exact₂ O hS ⊤ 0).linearEquivOfSurjective
    (cohOn.map_g_surjective O hS ⊤ 0 (h 1 one_pos))).length_eq
  have hr : LinearMap.range (cohOn.map O (Twist.map M
      (smulHom (structureModule Z.X) (Z.const g))) ⊤ 0) = LinearMap.range (LinearMap.lsmul O _ g) := by
    rw [hf]; rfl
  rw [Finset.sum_range_one, pow_zero, one_mul, ← Nat.cast_mul, Nat.cast_inj]
  refine (congrArg ENat.toNat (e'.symm.trans ?_)).trans
    ((ENat.toNat_mul _ _).trans (congrArg _ (ENat.toNat_natCast _)))
  exact (Submodule.quotEquivOfEq _ _ hr).length_eq.trans
    (((Submodule.quotEquivOfEq _ _ (Submodule.map_top _).symm).length_eq).trans
      (length_quotient_smul_top_dvr (coh (twist (structureModule Z.X) M) 0) g))

section Proj

open ProjSpace ProjCoh

variable (O) (N : ℕ)

theorem isNormalScheme_projSpace : IsNormalScheme (projSpace O N).X :=
  .of_pred (Models.isNormalScheme_projSpace O N)

abbrev formalTwistingSheaf : LB (projSpace O N).X := O1 O N

theorem algebraTop_projSpace : (projSpace O N).algebraTop = algebraSections O N ⊤ :=
  Algebra.algebra_ext _ _ fun r =>
    congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of O)).inv r))
      ((PSpace.str O N).app_eq_appLE (U := ⊤))


variable {O} in
theorem chiLen_projSpace {g : O} (hg : g ≠ 0) {j : ℕ} (hj : j ≤ N + 1) :
    chiLenPic O (divMod ((projSpace O (N + 1)).effConst g hg).1)
      (-(j : ℤ) • cls (formalTwistingSheaf O (N + 1)) (O1_isLB O _)) =
      if j = 0 then ((IsDiscreteValuationRing.addVal O g).toNat : ℤ) else 0 := by
  have hM := Twist.isLB_lbZPow (O1_isLB O (N + 1)) (-j)
  have H : ∀ A : Algebra O Γ(PSpace O (N + 1), ⊤), A = algebraSections O (N + 1) ⊤ →
      Module.Free O (coh (sheafO O (N + 1) (-j)) 0) ∧
      Module.finrank O (coh (sheafO O (N + 1) (-j)) 0) = (-j + (N + 1 : ℕ) : ℤ).toNat.choose (N + 1) := by
    rintro _ rfl
    exact ⟨inferInstance, finrank_coh_zero O (by omega) _⟩
  obtain ⟨h₁, h₂⟩ := H _ (algebraTop_projSpace O (N + 1))
  rw [← cls_lbZPow (O1_isLB O _) _ hM, chiLenPic_cls]
  refine (@chiLen_twist_effConst _ _ _ _ (projSpace O (N + 1)) _ hg _ hM
    (fun n hn => subsingleton_coh_of_neg_le O _ (by omega) hn) h₁).trans
    ((congrArg (fun n : ℕ => _ * (n : ℤ)) h₂).trans ?_)
  split_ifs with h
  · simp [h]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp


variable {O} in
theorem vDeg_div_projSpace {g : O} (hg : g ≠ 0) :
    (projSpace O (N + 1)).vDeg ((projSpace O (N + 1)).div g hg)
      (c1 (formalTwistingSheaf O (N + 1)) (O1_isLB O _) ^ (N + 1)) =
      (IsDiscreteValuationRing.addVal O g).toNat := by
  rw [← Fin.prod_const, div, vDeg_ofEff_prod, if_pos (by simp),
    interLen_eq_multiDiff O _ fun _ => O1_isLB O _, multiDiff_apply, Finset.sum_eq_single ∅]
  · have := chiLen_projSpace N hg (j := 0) (by omega)
    simp only [Nat.cast_zero, neg_zero, zero_smul, if_true] at this
    simp [this]
  · intro S _ hS
    have := chiLen_projSpace N hg (j := S.card) (by simpa using S.card_le_univ)
    rw [if_neg (by simpa using hS), neg_smul, natCast_zsmul] at this
    simp [this]
  · simp

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

theorem capDeg_divP_projSpace : ((projSpace O (N + 1)).toITh p).capDeg
    ((projSpace O (N + 1)).toITh p).divP (c1 (formalTwistingSheaf O (N + 1)) (O1_isLB O _) ^ (N + 1)) = 1 := by
  rw [capDeg_vp_toQ, divP, vDeg_div_projSpace]
  exact div_self (Nat.cast_ne_zero.2 (ramIdx_ne_zero O p))

theorem capDeg_divP_line : ((projSpace O 1).toITh p).capDeg ((projSpace O 1).toITh p).divP
    (c1 (formalTwistingSheaf O 1) (O1_isLB O 1)) = 1 := by
  rw [← pow_one (c1 _ _)]
  exact capDeg_divP_projSpace O 0 p



end Proj

end Model

end GlobalTheory.Vert
