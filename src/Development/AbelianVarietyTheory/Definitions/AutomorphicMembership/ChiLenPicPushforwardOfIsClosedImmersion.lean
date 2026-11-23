module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalFirstChernSurjective

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad

namespace NModel

section GenIso

variable {O : Type} [CommRing O] [IsLocalRing O] (Z : NModel O)

@[ext] structure GenIso (L L' : LB Z.X) : Type where

  u : ∀ (i : L.ι) (j : L'.ι), Γ(Z.X, Z.gen ⊓ (L.U i ⊓ L'.U j))ˣ

  rel : ∀ (i i₁ : L.ι) (j j₁ : L'.ι),
    res (inf_le_left : Z.gen ⊓ (L.U i ⊓ L'.U j) ⊓ (L.U i₁ ⊓ L'.U j₁) ≤ _) (u i j) *
      res (inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right) (L'.g j j₁) =
    res (inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left) (L.g i i₁) *
      res (inf_le_inf_right _ inf_le_left) (u i₁ j₁)

namespace GenIso

variable {Z} {L L' L'' : LB Z.X} (φ : Z.GenIso L L')

def pair (hL : L.IsLB) (hL' : L'.IsLB) : VPair Z :=
  .ofUnits (LB.div L L') (Semi.LB.isLB_div hL hL') (fun p => (φ.u p.1 p.2).val) (fun _ => Units.isUnit _) fun p q => by
    have := congrArg Units.val (eq_mul_inv_iff_mul_eq.2 (φ.rel p.1 q.1 p.2 q.2))
    rw [mul_right_comm] at this
    refine this.trans (congrArg (· * _) ?_)
    change _ = (res _ (res _ _ * (res _ _)⁻¹)).val
    rw [map_mul, map_inv]
    exact congrArg Units.val (congrArg₂ (fun a b => a * b⁻¹) (Semi.LB.res_res _ _ _) (Semi.LB.res_res _ _ _)).symm

def dual : Z.GenIso (CechPic.dual L) (CechPic.dual L') where
  u i j := (φ.u i j)⁻¹
  rel i i₁ j j₁ := by
    have := congrArg (·⁻¹) (φ.rel i i₁ j j₁)
    simp only [mul_inv, ← map_inv] at this
    exact this


end GenIso

end GenIso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

namespace GenIso

variable {L L' L'' : LB Z.X} (φ : Z.GenIso L L') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)

def smul (g : O) (hg : g ≠ 0) : Z.GenIso L L where
  u i j := (Z.isUnit_const hg inf_le_left).unit * res inf_le_right (L.g i j)
  rel i i₁ j j₁ := by
    refine unit_ext fun y hy => ?_
    have e (a b : L.ι) (h : y ∈ Z.gen ⊓ (L.U a ⊓ L.U b)) :
        gm (𝟙 Z.X) y _ (Z.isUnit_const hg (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _)).unit =
          gm (𝟙 Z.X) y _ (Z.isUnit_const hg le_rfl).unit := by
      rw [← gm_res (𝟙 Z.X) y (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _) h]
      exact congrArg _ (Units.ext (resG_resG _ _ _).symm)
    have h₁ : y ∈ Z.gen ⊓ (L.U i₁ ⊓ L.U j₁) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 Z.X) y _ hy, gm_res (𝟙 Z.X) y _ hy.1, gm_res (𝟙 Z.X) y _ h₁, e _ _ hy.1, e _ _ h₁]
    rw [mul_assoc, gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.1.2.2 hy.2.2, mul_left_comm,
      gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.2.1 hy.2.2]

def div : Z.VDivZ := (φ.pair hL hL').cls

@[simp] theorem vCls_div : Z.vCls (φ.div hL hL') = cls L hL - cls L' hL' := (vCls_cls _).trans (cls_div _ _ _)

@[simp] theorem div_smul (g : O) (hg : g ≠ 0) : (smul hL g hg).div hL hL = Z.div g hg := by
  refine (VPair.cls_eq_iff.2 (VPair.isIsom_of_units
    (P' := (smul hL g hg).pair hL hL) (fun p _ => res inf_le_left (L.g p.1 p.2)) fun p q => ?_)).symm
  change resG _ _ (resG _ _ _ * resG _ _ _) = resG _ _ (resG _ _ _) * resG _ _ (resG _ _ _)
  rw [map_mul, mul_comm]
  exact congrArg₂ (· * ·) ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)
    ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)

end GenIso

variable (Z)

abbrev VDivQ : Type := ℚ ⊗[ℤ] Z.VDivZ


variable {Z} in
def toQ : Z.VDivZ →+ Z.VDivQ := (TensorProduct.mk ℤ ℚ Z.VDivZ 1).toAddMonoidHom

def cDQ : Z.VDivQ →ₗ[ℚ] PicSym Z.X := LinearMap.liftBaseChange ℚ (firstChernPic.comp Z.vCls).toIntLinearMap

def capDeg_vp (p d : ℕ) : Z.VDivQ →ₗ[ℚ] PicSym Z.X →ₗ[ℚ] ℚ :=
  (ramIdx O p : ℚ)⁻¹ • LinearMap.liftBaseChange ℚ (Z.vDeg d).toIntLinearMap

variable {Z}

@[simp] theorem cDQ_toQ (D : Z.VDivZ) : Z.cDQ (toQ D) = firstChernPic (Z.vCls D) := by simp [cDQ, toQ]

theorem capDeg_vp_toQ (p d : ℕ) (D : Z.VDivZ) (Q : PicSym Z.X) :
    Z.capDeg_vp p d (toQ D) Q = Z.vDeg d D Q / ramIdx O p := by
  simp [capDeg_vp, toQ, div_eq_inv_mul]

theorem capDeg_vp_eq_zero (p : ℕ) {d n : ℕ} (D : Z.VDivQ) (hn : n ≠ d) {x : PicSym Z.X}
    (hx : x ∈ symDeg (SmallPic Z.X) n) : Z.capDeg_vp p d D x = 0 := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D => simp [capDeg_vp, vDeg_eq_zero D hn hx]
  | add a b ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]

section Theory

variable (Z) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def divP : Z.VDivZ := Z.div p (natCast_ne_zero O p)


set_option linter.overlappingInstances false in
@[reducible] def toITh [CharP (ResidueField O) p] (d : ℕ) : Formalism.BasicNotions.DV.ITh where
  LB := FinLB Z.X
  Ch := PicSym Z.X
  c1 := FinLB.c1
  VDiv := Z.VDivQ
  cD := Z.cDQ
  capDeg := Z.capDeg_vp p d
  divP := toQ (Z.divP p)
  cD_divP := by simp [divP]
  dim := d + 1

end Theory


variable (Z) in
def vdiv (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : Z.VDivQ := toQ (u.div L.isLB L'.isLB)

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : L'.c1 = L.c1 - Z.cDQ (Z.vdiv L L' u) := by
  rw [vdiv, cDQ_toQ, GenIso.vCls_div, map_sub]
  exact (sub_sub_cancel _ _).symm

theorem vdiv_smul (L : FinLB Z.X) (g : O) (hg : g ≠ 0) : Z.vdiv L L (.smul L.isLB g hg) = toQ (Z.div g hg) :=
  congrArg toQ (GenIso.div_smul L.isLB g hg)

end NModel

theorem chiLenPic_pushforward_of_isClosedImmersion {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
    [Algebra R Γ(Y, ⊤)] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : ∀ r : R, i.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r) (H : Y.Modules) :
    chiLenPic R ((Scheme.Modules.pushforward i).obj H) = chiLenPic R H ∘ pull i := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  refine (chiLen_congr R (Twist.projIso M i H)).symm.trans ?_
  rw [chiLen_eq_of_linearEquiv R fun n => LinearEquiv.ofBijective _
    (cohPushMap_bijective_of_isClosedImmersion R i hi _ ⊤ n)]
  rfl

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Model O} {f : B'.X ⟶ B.X} [IsIso f]
  (hf : f ≫ B.str = B'.str)


variable (f) in
include f in
theorem relDim_eq_of_isIso : B'.relDim = B.relDim := by
  refine Model.relDim_eq_iff.2 (Eq.trans ?_ B.dim_eq)
  rw [← topologicalKrullDim_eq_of_isEmbedding f.isOpenEmbedding.isEmbedding f.surjective.range_eq,
    topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id]

theorem vDeg_vPull_of_isIso (D : B.VDivZ) (x : PicSym B.X) :
    B'.vDeg (Model.vPull hf D) (picSymPull f x) = B.vDeg D x := by
  have key (I : B.effVert) : B'.vDeg (Model.vPull hf (Model.ofEff I)) (picSymPull f x) = B.vDeg (Model.ofEff I) x := by
    let g := (I.1.comapIso f).hom ≫ pullback.snd _ _
    have hg : (I.1.comap f).subschemeι ≫ f = g ≫ I.1.subschemeι := by
      simp [g, ← pullback.condition]
    have e : (Scheme.Modules.pushforward f).obj (divMod (I.1.comap f)) ≅ divMod I.1 :=
      (Scheme.Modules.pushforwardComp _ _ ≪≫ Scheme.Modules.pushforwardCongr hg ≪≫
        (Scheme.Modules.pushforwardComp _ _).symm).app _ ≪≫
        ((Scheme.Modules.pushforward I.1.subschemeι).mapIso (asIso (unitToPush g))).symm
    have h := (chiLenPic_congr O e).symm.trans
      (chiLenPic_pushforward_of_isClosedImmersion O f (Model.appTop_const hf) _)
    refine LinearMap.congr_fun (picSym_linearMap_ext
      (l := B'.vDeg (Model.vPull hf (Model.ofEff I)) ∘ₗ (picSymPull f).toLinearMap) fun n c => ?_) x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, picSymPull_c1Pic, Model.vPull_ofEff,
      Model.vDeg_ofEff, Model.effDeg, Model.IsVertical.deg, picForm_prod, relDim_eq_of_isIso f]
    rw [h, multiDiff_comap, Function.comp_apply, map_zero]
    rfl
  obtain ⟨I, J, rfl⟩ := Model.exists_eq_ofEff_sub D
  simp only [map_sub, LinearMap.sub_apply, key]

end Iso

namespace NModel

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

theorem vDeg_div_of_cover {ι : Type} [Fintype ι] {B : ι → Model O} (f : ∀ i, (B i).X ⟶ Z.X) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ i, f i ≫ Z.str = (B i).str) (hc : ∀ x, ∃ i, x ∈ Set.range (f i))
    (hd : ∀ i j, (Set.range (f i) ∩ Set.range (f j)).Nonempty → i = j) (d : ℕ) {g : O} (hg : g ≠ 0) (x : PicSym Z.X) :
    Z.vDeg d (Z.div g hg) x = ∑ i ∈ Finset.univ.filter fun i => (B i).relDim = d,
      (B i).vDeg ((B i).div g hg) (picSymPull (f i) x) := by
  have hirr (i) : IsIrreducible (Set.range (f i)) := by
    simpa using (IrreducibleSpace.isIrreducible_univ (B i).X).image _ (f i).continuous.continuousOn
  have hmem (i) : Set.range (f i) ∈ irreducibleComponents Z.X := ⟨hirr i, fun T hT hle y hy => by
    obtain ⟨j, hj⟩ := hc y
    obtain ⟨z, -, hz⟩ := hT.2 _ _ (f i).isOpenEmbedding.isOpen_range (f j).isOpenEmbedding.isOpen_range
      ((hirr i).1.mono fun _ h => ⟨hle h, h⟩) ⟨y, hy, hj⟩
    exact hd i j ⟨z, hz⟩ ▸ hj⟩
  let σ : ι → Z.Comp := fun i => ⟨_, hmem i⟩
  have hσ : Function.Bijective σ := ⟨fun i j h => hd i j (by
      rw [show Set.range (f j) = Set.range (f i) from (congrArg Subtype.val h).symm, Set.inter_self]
      exact (hirr i).1), fun C => by
    obtain ⟨y, hy⟩ := C.2.1.1
    obtain ⟨i, hi⟩ := hc y
    exact ⟨i, Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents (hmem i) C.2 hi hy)⟩⟩
  let e (i) : (B i).X ≅ (Z.comp (σ i)).X :=
    IsOpenImmersion.isoOfRangeEq (f i) (σ i).opens.ι (Scheme.Opens.range_ι (σ i).opens).symm
  have he (i) : (e i).hom ≫ Z.compι (σ i) = f i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' (i) : (e i).hom ≫ (Z.comp (σ i)).str = (B i).str := by rw [← compι_str, ← Category.assoc, he, hf]
  rw [vDeg_apply, Finset.sum_filter, Finset.sum_filter, ← hσ.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [relDim_eq_of_isIso (e i).hom, vRes_div, ← vDeg_vPull_of_isIso (he' i), Model.vPull_div, ← he]
  refine if_congr Iff.rfl (congrArg _ ?_) rfl
  refine LinearMap.congr_fun (picSym_linearMap_ext (l := (picSymPull _).toLinearMap ∘ₗ (picSymPull _).toLinearMap)
    (l' := (picSymPull _).toLinearMap) fun n c => ?_) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, picSymPull_c1Pic, pull_comp]

def sigma {ι : Type} [Finite ι] (B : ι → Model O) [∀ i, GlobalTheory.IsNormalScheme (B i).X] : NModel O where
  X := ∐ fun i => (B i).X
  str := Sigma.desc fun i => (B i).str
  isProjOver := ProjSpace.isProjOver_sigmaDesc _ fun i => (B i).isProjOver
  flat := IsZariskiLocalAtSource.sigmaDesc fun i => (B i).flat

section Example

variable (O) (n N : ℕ) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def copies : NModel O :=
  haveI := Model.isNormalScheme_projSpace O N
  sigma fun _ : Fin n => Model.projSpace O N

def twistingSheafOnCopies : FinLB (copies O n N).X :=
  FinLB.pull ⟨N + 1, (ProjSpace.O1 O N).U, (ProjSpace.O1 O N).g, ProjSpace.O1_isLB O N⟩
    (Sigma.desc fun _ : Fin n => 𝟙 (PSpace O N))

theorem capDeg_divP_copies : ((copies O n (N + 1)).toITh p (N + 1)).capDeg ((copies O n (N + 1)).toITh p (N + 1)).divP
    ((twistingSheafOnCopies O n (N + 1)).c1 ^ (N + 1)) = n := by
  have h (i : Fin n) : picSymPull (Sigma.ι (fun _ : Fin n => (Model.projSpace O (N + 1)).X) i)
      ((twistingSheafOnCopies O n (N + 1)).c1 ^ (N + 1)) = c1 (Model.formalTwistingSheaf O (N + 1)) (ProjSpace.O1_isLB O _) ^ (N + 1) := by
    refine (map_pow _ _ _).trans (congrArg (· ^ (N + 1)) ((picSymPull_c1Pic _ _).trans (congrArg firstChernPic ?_)))
    refine (congrArg _ (FinLB.cls_pull _ _)).trans ((pull_comp _ _ _).symm.trans ?_)
    erw [Sigma.ι_desc, pull_id]
    rfl
  rw [capDeg_vp_toQ, divP, vDeg_div_of_cover (Z := copies O n (N + 1)) (B := fun _ : Fin n => Model.projSpace O (N + 1))
    (fun i => Sigma.ι (fun _ : Fin n => (Model.projSpace O (N + 1)).X) i) (fun i => Sigma.ι_desc _ _)
    (fun x => (sigmaOpenCover _).exists_eq x)
    (fun i j ⟨x, hi, hj⟩ => by_contra fun hij => Set.disjoint_left.1
      (Opens.coe_disjoint.2 (disjoint_opensRange_sigmaι _ i j hij)) hi hj)]
  refine (congrArg (· / (ramIdx O p : ℚ)) (Finset.sum_congr rfl fun i _ =>
    (congrArg _ (h i)).trans (Model.vDeg_div_projSpace N (natCast_ne_zero O p)))).trans ?_
  simp only [Model.relDim_projSpace, Finset.filter_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_div_cancel_right₀ (n : ℚ) (b := ramIdx O p) (Nat.cast_ne_zero.2 (ramIdx_ne_zero O p))

end Example

end NModel

section Mdl

open NumberField GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

@[reducible] def nmodel (Z : Mdl Y i₀) : NModel (Z.i.c.V W) where
  X := Z.X
  str := Z.s
  normal := Z.normal
  isProjOver := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  flat := Z.flat

theorem natCast_mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp.ne_zero
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isDiscreteValuationRing_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) :=
  haveI := c.fin
  haveI : NumberField c.F := {}
  (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero
    (natCast_mem_nonunits_V c hp hW)).1

theorem charP_residueField_of_mem_nonunits {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    CharP (ResidueField (c.V W)) p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  rw [← map_natCast (residue (c.V W)), residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact_mod_cast natCast_mem_nonunits_V c hp hW

abbrev GenIso (Z : Mdl Y i₀) (L L' : FinLB Z.X) : Type := (nmodel Z).GenIso L.lb L'.lb

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (d : ℕ)

@[reducible] def ithOf : Formalism.BasicNotions.DV.ITh :=
  haveI := Fact.mk hp
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits Z.i.c hp hW
  (nmodel Z).toITh p d

variable {Z}

def vdiv (L L' : FinLB Z.X) (u : GenIso Z L L') : (ithOf hp hW Z d).VDiv :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  (nmodel Z).vdiv L L' u

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : GenIso Z L L') :
    (ithOf hp hW Z d).c1 L' = (ithOf hp hW Z d).c1 L - (ithOf hp hW Z d).cD (vdiv hp hW d L L' u) :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  NModel.firstChern_eq_sub_divisor (Z := nmodel Z) L L' u

def fpairOf {r : ℕ} (x x' : Fin r → FinLB Z.X) (u : ∀ i, GenIso Z (x i) (x' i)) :
    Formalism.BasicNotions.DV.FPair (ithOf hp hW Z d) r :=
  ⟨x, x', fun i => vdiv hp hW d _ _ (u i), fun i => firstChern_eq_sub_divisor hp hW d _ _ (u i)⟩

include hp hW

theorem gen_eq_basicOpen : (nmodel Z).gen = Z.X.basicOpen (p : Γ(Z.X, ⊤)) := by
  have := Fact.mk hp
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have := charP_residueField_of_mem_nonunits Z.i.c hp hW
  rw [(nmodel Z).gen_eq_basicOpen (natCast_ne_zero _ p) (natCast_mem_maximalIdeal _ p), map_natCast]

theorem mem_gen_iff_inQ {x : Z.X} : x ∈ (nmodel Z).gen ↔ Z.inQ x := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have h (g : Z.i.c.V W) : (Z.X.evaluation ⊤ x trivial).hom ((nmodel Z).const g) ≠ 0 ↔
      x ∈ Z.X.basicOpen ((nmodel Z).const g) := Z.X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) x trivial _
  refine ⟨fun hx => charZero_of_inj_zero fun n hn => by_contra fun h0 => ?_, fun hx => ?_⟩
  · exact (h n).2 ((nmodel Z).gen_le_basicOpen (Nat.cast_ne_zero.2 h0) hx) (by simpa using hn)
  · have : CharZero (Z.X.residueField x) := hx
    rw [gen_eq_basicOpen hp hW, ← map_natCast (nmodel Z).const, ← h]
    simpa using hp.ne_zero

theorem chart_le_gen (a : Fin Z.m) : (Z.U a).1 ≤ (nmodel Z).gen := by
  rw [gen_eq_basicOpen hp hW]
  refine le_basicOpen_of_isUnit le_top ?_
  rw [map_natCast, ← map_natCast (Z.alg a)]
  exact (Ne.isUnit (Nat.cast_ne_zero.2 hp.ne_zero)).map _

end Mdl

end GlobalTheory.ShFam.Pad
