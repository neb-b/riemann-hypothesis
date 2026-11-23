module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.PrincipalNumerics

theorem sectionsFiniteDimension_one_trivial_transitions {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K)
    (hp : Function.Bijective p.appTop.hom) {M : LB X} (hM : M.IsLB) (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hc : ∀ (U : X.Opens) (a : K), constFn p U a = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) := fun U a => rfl
  have hb : Function.Bijective (fun a : K => p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
    hp.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨s, hs, hu⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun i => homOfLE le_top) hM.cover.ge t.f (fun i j => by
    have := t.compat i j
    rw [hg, Units.val_one, _root_.one_mul] at this
    exact this)
  obtain ⟨a, rfl⟩ := hb.2 s
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · rw [Fin.sum_univ_one, _root_.mul_one, hc]
    exact (hs j).symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine hb.1 (hu _ fun j => ?_)
    have := hb' j
    rw [Fin.sum_univ_one, _root_.mul_one, hc] at this
    exact this.symm

variable {K : Type} [Field K]

theorem vol_one [IsAlgClosed K] (hH : Out.GlobalSectionsRankAlgClosed) (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) :
    Vol P.A.hom P.L P.g 1 := by
  refine ⟨fun e => if e = 0 then 1 else e ^ P.g, fun e => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · refine sectionsFiniteDimension_one_trivial_transitions _ (hG _ P.A P.isAb) (DVR.linComb_isLB _ P.isLB _ _) fun i j => ?_
      show ∏ _ : PUnit.{1}, (_ : Γ(P.A.left, LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) i ⊓
        LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) j)ˣ) ^ (0 : ℤ) = 1
      simp only [zpow_zero, Finset.prod_const_one]
    · simp only [if_neg he.ne']
      exact PowSec.exists_basis_sections hH K P e he
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with e he
    have : (e : ℝ) ^ P.g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 he.ne')
    rw [if_neg he.ne', Nat.cast_pow, div_self this]

theorem formIs_id (P : Out.PolAV (Sp K)) : FormIs P P.L (𝟙 P.A) := by
  refine ⟨inferInstance, ?_⟩
  rw [Category.comp_id]
  exact PolBaseChange.lbIso_refl (DVR.linComb_isLB _ P.isLB _ _)

theorem symB (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) : SymB P.L := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  have le : ∀ j : (PUnit → P.L.ι) × P.L.ι, (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left).U j.1 ⊓ P.L.U j.2 ≤
      LB.wchart P.L (![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
  refine gen_chartPull (h := 𝟙 _) (A' := LB.div (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) P.L)
    (A := LB.LinComb P.L (K := Fin 2) ![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] ![1, -1])
    ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' => ?_⟩ u hu
  refine (gm_div P.L (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
    (Eq.trans ?_ (gm_linComb P.L _ _ (𝟙 _) y _ _ (le j hj) (le j' hj')).symm)
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
  · exact (gm_pull_g P.L _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
  · exact (zpow_neg_one _).symm

theorem mapDeg_id (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := MapDeg.id_one X

theorem exists_basis_of_pairing {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ y : G, y ^ k = 1 →
      ∃! c : Fin (2 * g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have : NeZero k := ⟨hk.ne'⟩
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* Rˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing k g T R ze hk hz (fun x => Subtype.ext x.2)
    (fun d hd => by
      rw [← hc d hd]
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩,
        fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩
      obtain ⟨c, hc⟩ := hd
      show x.1 ^ _ = 1
      rw [hc, pow_mul, x.2, one_pow]) e (fun x => (hw' _ _ _ (halt _ x.2)).symm)
    (fun x hx => Subtype.ext (hnd _ x.2 fun y hy => by
      have h : w x ⟨y, hy⟩ = 1 := hx ⟨y, hy⟩
      exact h ▸ hw x ⟨y, hy⟩))
  have cm : ∀ a b : G, Commute a b := fun a b => _root_.mul_comm a b
  have tor : ∀ i, (v i).1 ^ k = 1 := fun i => (v i).2
  have inj := LevelOfPairing.injective_comb cm hW hmul hz (fun i => (v i).1) tor
    (fun i j => (show w (v i) (v j) = _ from hv i j) ▸ hw _ _)
  refine ⟨fun i => (v i).1, tor, fun y hy => ?_⟩
  obtain ⟨c, hcy⟩ := LevelOfPairing.surjective_comb cm hk.ne' _ tor (hc k dvd_rfl) inj y hy
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
  · simpa only [ZMod.val_cast_of_lt (c _).2] using hcy
  · have := inj (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hcy.symm)
    funext i
    rw [← this]
    exact (ZMod.natCast_zmod_val _).symm

theorem exists_torsBasis [IsAlgClosed K] (hL : Out.Laws) (P : Out.PolAV (Sp K)) (k : ℕ) (hk : (k : K) ≠ 0) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Out.baseOver _)
  refine Exists.imp (fun pt h => ⟨Nat.pos_of_ne_zero hk0, h⟩) ?_
  exact exists_basis_of_pairing (G := Out.baseOver _ ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K (𝟙 _) (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (hL.weilNondeg K P _ hk)

theorem actsBy_id (P : Out.PolAV (Sp K)) {k m : ℕ} (hk0 : 0 < k) (hk : k ≠ 1) (pt : Fin m → (Out.baseOver (Sp K) ⟶ P.A)) :
    ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k)) := by
  have := P.isAb.comm
  refine ⟨hk0, fun i => ?_⟩
  rw [Category.comp_id, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i (fun b _ hb => by
    rw [Matrix.one_apply_ne hb, ZMod.val_zero, pow_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Matrix.one_apply_eq, ZMod.val_one'' hk, pow_one]

end GlobalTheory.PrincipalNumerics


open GlobalTheory.PrincipalNumerics in
theorem GlobalTheory.principal_polarisation_numerics : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  intro hL _ K _ _ P
  refine ⟨vol_one hL.globalSectionsRank hL.globalFns P, formIs_id P, symB hL.globalFns P, mapDeg_id _,
    GlobalTheory.veryAmple_lbPow hL.ample K P 4 le_rfl, fun k hk => ?_⟩
  obtain ⟨pt, hpt⟩ := exists_torsBasis hL P k hk
  exact ⟨pt, hpt, fun h => actsBy_id P hpt.pos h pt⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X}
    (H : LBIso L' (L.pull φ)) (φ' : X'' ⟶ X') : LBIso (L'.pull φ') (L.pull (φ' ≫ φ)) :=
  LBIso.chartPull (chartPullPull L' φ' φ' rfl) (chartPullSame L _ _ _ φ' fun _ => rfl) H

theorem TMap.refl (t : TObj g k J b s) : TMap t t (𝟙 S) := by
  refine ⟨𝟙 _, ?_, ?_, fun i => by simp, fun j => by simp⟩
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact isGrpPullback_of_iso (Iso.refl t.A)
  · exact LBIso.chartPull (chartPullId t.L) (chartPullPull t.L _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl t.isLB)

theorem TMap.comp {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨φ', k₁, k₂, k₃, k₄⟩ := h'
  refine ⟨φ' ≫ φ, k₁.comp h₁, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) k₂ (lbIso_pull_comp h₂ φ')
  · rw [← Category.assoc, k₃, Category.assoc, h₃, Category.assoc]
  · rw [← Category.assoc, k₄, Category.assoc, h₄, Category.assoc]

theorem TMap.cancel {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨ψ, k₁, k₂, k₃, k₄⟩ := n
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : t''.A.left ⟶ t'.A.left, F ≫ φ = ψ ∧ F ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ψ (t''.A.hom ≫ f') (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc, Category.assoc, h₃]
    · have a₁ : (t''.pt i).left ≫ t''.A.hom = 𝟙 S'' := Over.w (t''.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 S' := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tmap_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => ⟨TMap.refl t, fun _ _ h => ⟨fun h' => h'.comp h, fun n => h.cancel n⟩⟩

end GlobalTheory.ZM
end
end

