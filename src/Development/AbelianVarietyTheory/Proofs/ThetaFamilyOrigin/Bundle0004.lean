module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PolAgree

open FieldDescentGen

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem crd_pull {X Y : Scheme.{0}} (φ : X ⟶ Y) (H : LB Y) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R]
    (y : Sp R ⟶ X) (v : J → R) (h : Crd H s (y ≫ φ) v) :
    Crd (H.pull φ) (fun j => secPull H φ (s j)) y v := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hl' : ⊤ ≤ y ⁻¹ᵁ (H.pull φ).U (fun _ => l) := fun z hz => mem_pull.2 (hl hz)
  refine ⟨fun _ => l, c, hl', fun j => ?_⟩
  rw [hv j]
  congr 1
  unfold valR
  rw [dite_eq_left hl, dite_eq_left hl']
  congr 1
  change _ = (y.appLE _ ⊤ hl').hom ((φ.appLE _ _ (pull_le H φ (fun _ => l))).hom ((s j).f l))
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem mulA_comp {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (m : ℕ) :
    Out.mulA A m ≫ φ = φ ≫ Out.mulA B m := by
  unfold Out.mulA
  rw [MonObj.comp_pow, Category.comp_id]
  have := map_pow (IsMonHom.monoidHom φ A) (𝟙 A) m
  simpa using this

theorem lbIso_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  intro h K _ _ P P' N m J s s' a θ θ' φ hm hφ hs hcrd hθ hP hP'
  have := polAV_isIntegral_of_isAlgClosed K P
  have hL := P.isLB
  have hL' := P'.isLB
  have hN : (lbPow P.L N).IsLB := LB.isLB_linComb hL _ _
  have hN' : (lbPow P'.L N).IsLB := LB.isLB_linComb hL' _ _
  have h1 : (lbPow P.L 1).IsLB := LB.isLB_linComb hL _ _
  have h1' : (lbPow P'.L 1).IsLB := LB.isLB_linComb hL' _ _
  have hmul := h.mulN _ P m hm
  have hfl : Flat (Out.mulA P.A m).left := hmul.2.1
  have hsu : Surjective (Out.mulA P.A m).left := hmul.2.2.1
  have hc : (Out.mulA P.A m).left ≫ φ.left = φ.left ≫ (Out.mulA P'.A m).left := by
    rw [← Over.comp_left, mulA_comp, Over.comp_left]
  have hw := CrdIso.exists_chart_unit (H := lbPow P.L N) (H' := (lbPow P'.L N).pull φ.left) (s := s)
    (s' := fun j => secPull _ φ.left (s' j)) hs (fun F _ y v hv => crd_pull _ _ _ _ _ (hcrd F y v hv))
  have key : LBIso (lbPow P.L 1) ((lbPow P'.L 1).pull φ.left) := by
    refine _root_.GlobalTheory.AssocDescent.lbIso_of_associated _ _ (Out.mulA P.A m).left _ _ θ (secPull _ φ.left θ') h1 (LB.isLB_pull h1' _) hθ fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hN y
    obtain ⟨k', hk'⟩ := exists_chart hN' (φ.left y)
    obtain ⟨l, hl⟩ := exists_chart h1 ((Out.mulA P.A m).left y)
    obtain ⟨l', hl'⟩ := exists_chart h1' (φ.left ((Out.mulA P.A m).left y))
    have hl'' : (Out.mulA P'.A m).left (φ.left y) ∈ (lbPow P'.L 1).U l' := by
      rw [← Scheme.Hom.comp_apply, ← hc]; exact hl'
    have hlp : (Out.mulA P.A m).left y ∈ ((lbPow P'.L 1).pull φ.left).U (fun _ => l') := mem_pull.2 hl'
    have hkp : y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') := mem_pull.2 hk'
    refine ⟨l, fun _ => l', hl, hlp, ?_⟩
    have e1 : gs (Out.mulA P.A m).left y _ ((secPull _ φ.left θ').f (fun _ => l')) =
        (φ.left.stalkMap y).hom (gs (Out.mulA P'.A m).left (φ.left y) _ (θ'.f l')) := by
      rw [← gs_comp _ _ _ _ hl'', ← hc]
      exact gs_appLE _ _ _ _ _ _ hlp _
    have e2 : gs (𝟙 P.A.left) y _ ((secPull _ φ.left (s' a)).f (fun _ => k')) =
        (φ.left.stalkMap y).hom (gs (𝟙 P'.A.left) (φ.left y) _ ((s' a).f k')) := by
      rw [← gs_stalkMap _ _ _ hk']
      exact (gs_appLE _ _ _ _ _ _ hkp _).trans (by rw [Category.id_comp])
    obtain ⟨w, hw⟩ := hw k (fun _ => k')
    have hx : (𝟙 P.A.left : _ ⟶ _) y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') ⊓ (lbPow P.L N).U k :=
      ⟨hkp, hk⟩
    have e := congrArg (gs (𝟙 P.A.left) y _) (hw a)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, gs_unit _ _ _ hx, e2] at e
    have a1 := (hP' (φ.left y) k' l' hk' hl'').map (φ.left.stalkMap y).hom
    rw [e1]
    refine (hP y k l hk hl).symm.trans (Associated.trans ?_ a1)
    exact ⟨_, (_root_.mul_comm _ _).trans e.symm⟩
  have oneIso {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) : LBIso (lbPow L 1) L := by
    apply CechPic.iso_of_chart hL
    refine ⟨fun j => j PUnit.unit, fun _ _ hy => Set.mem_iInter.1 hy PUnit.unit, ?_⟩
    intro y p q hp hq
    refine (gm_linComb L _ _ (𝟙 X) y p q hp hq).trans ?_
    simp
  have pullOne {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : Y ⟶ X) :
      LBIso ((lbPow L 1).pull f) (L.pull f) := by
    apply CechPic.iso_of_chart (LB.isLB_pull hL f)
    refine ⟨fun j _ => j PUnit.unit PUnit.unit, fun _ _ hy => mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hy) PUnit.unit), ?_⟩
    intro y p q hp hq
    refine (gm_pull_g (lbPow L 1) f (𝟙 Y) y p q hp hq).trans ?_
    refine (gm_linComb L _ _ (𝟙 Y ≫ f) y _ _ (mem_pull.1 hp) (mem_pull.1 hq)).trans ?_
    simpa using (gm_pull_g L f (𝟙 Y) y (fun _ => p PUnit.unit PUnit.unit) (fun _ => q PUnit.unit PUnit.unit) (mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hp) PUnit.unit)) (mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hq) PUnit.unit))).symm
  have e := (CechPic.cls_eq_iff h1 (LB.isLB_pull h1' _)).2 key
  have e1 := (CechPic.cls_eq_iff h1 hL).2 (oneIso P.L hL)
  have e2 := (CechPic.cls_eq_iff (LB.isLB_pull h1' _) (LB.isLB_pull hL' _)).2 (pullOne P'.L hL' φ.left)
  rw [e1, e2] at e
  exact (CechPic.cls_eq_iff (LB.isLB_pull hL' _) hL).1 e.symm

end GlobalTheory.ZH.PolAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoLevels

open ReciprocityTheory.ChartRestriction.G.Out ThetaCoord CommPairing GlobalLift VVRank

theorem labelSymp_eq {g M : ℕ} (a b : Fin (2 * g) → ZMod M) :
    labelSymp a b = Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : ZMod M)) a b := by
  rw [labelSymp, Matrix.toBilin'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply]; ring

theorem labelSymp_swap {g M : ℕ} (a b : Fin (2 * g) → ZMod M) : labelSymp a b = -labelSymp b a := by
  have h : ∀ i j, stdSymp g i j = -stdSymp g j i := fun i j => by
    unfold stdSymp
    split_ifs <;> omega
  rw [labelSymp, labelSymp, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j i]; push_cast; ring

theorem eq_of_proportional {R : Type} [CommRing R] [IsDomain R] {g n j N' : ℕ} (hn : Odd n) (hN : N' = n ^ j)
    {ζ : Rˣ} (hζ : IsPrimitiveRoot ζ (N' ^ 2))
    (σ : (Fin (2 * g) → ZMod (N' ^ 2)) →ₗ[ZMod (N' ^ 2)] (Fin (2 * g) → ZMod (N' ^ 2)))
    (hσ : ∀ a b, labelSymp (σ a) (σ b) = labelSymp a b) (hm : ∀ a, N' • σ a = N' • a)
    (v : (Fin (2 * g) → ZMod (N' ^ 2)) → R) (u u' : Rˣ) (hu : ∀ a, u * v (σ a) = u' * v a)
    (hr : ∀ a b, v a = (ζ ^ thetaRelExp N' 1 a b : Rˣ) * v (a + N' • b))
    (hs : ∀ c, ∃ d, v (c + n • d) ≠ 0) (a : Fin (2 * g) → ZMod (N' ^ 2)) : σ a = a := by
  have ho : Odd N' := hN ▸ hn.pow
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  let ω := Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : ZMod (N' ^ 2)))
  let S := σ - LinearMap.id
  have hb : ∀ a, ∃ b, S a = N' • b := fun a => by
    have h : N' • S a = 0 := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, smul_sub, hm, sub_self]
    choose b hb using fun i => exists_eq_nsmul_of_nsmul_eq_zero_zmod ho.pos.ne' le_rfl (S a i) (congrFun h i)
    exact ⟨b, funext hb⟩
  have e : ∀ a, σ a = a + S a := fun a => by simp [S]
  have sw : ∀ a b, ω a b = -ω b a := fun a b => by
    rw [← labelSymp_eq, ← labelSymp_eq, labelSymp_swap]
  have hS : ∀ a b, ω (S a) b = ω (S b) a := fun a b => by
    have h := hσ a b
    rw [labelSymp_eq, labelSymp_eq, e, e] at h
    have h₀ : ω (S a) (S b) = 0 := by
      obtain ⟨x, hx⟩ := hb a
      obtain ⟨y, hy⟩ := hb b
      rw [hx, hy, map_nsmul, map_nsmul, LinearMap.smul_apply, ← mul_smul, ← sq, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul]
    change ω _ _ = ω _ _ at h
    simp only [map_add (f := _), LinearMap.add_apply] at h
    rw [sw (S b)]
    linear_combination h - h₀
  let q : (Fin (2 * g) → ZMod (N' ^ 2)) → ZMod (N' ^ 2) := fun a => (((N' ^ 2 + 1) / 2 : ℕ) : ZMod (N' ^ 2)) * ω a (S a)
  have h₁ : ∀ a, v a ≠ 0 → ζ ^ (q a).val * u' = u := fun a ha => by
    obtain ⟨b, hb⟩ := hb a
    have h := hr a b
    rw [thetaRelExp, one_pow, Nat.one_mul, ← hb, ← e, labelSymp_eq] at h
    refine Units.ext (mul_right_cancel₀ ha ?_)
    rw [Units.val_mul, _root_.mul_assoc, ← hu, mul_left_comm]
    exact congrArg _ h.symm
  obtain ⟨d₀, hd₀⟩ := hs 0
  have h0 : S = 0 := end_eq_zero_of_quad_const_on_cosets (isUnit_two_zmod_pow ho 2) (r := (n : ZMod (N' ^ 2)))
    ⟨j * 2, by rw [← Nat.cast_pow, pow_mul, ← hN, ZMod.natCast_self]⟩ ω (injective_toBilin'_stdSymp g) S hS (-1) q
    (fun x => by
      have : (2 : ZMod (N' ^ 2)) * (((N' ^ 2 + 1) / 2 : ℕ) : ZMod (N' ^ 2)) = 1 := by
        rw [show (2 : ZMod (N' ^ 2)) = ((2 : ℕ) : ZMod (N' ^ 2)) from Nat.cast_ofNat.symm, ← Nat.cast_mul,
          Nat.mul_div_cancel' ho.pow.add_one.two_dvd, Nat.cast_add,
          ZMod.natCast_self, zero_add, Nat.cast_one]
      rw [← _root_.mul_assoc, this, sw x]; simp)
    {t | v t ≠ 0}
    (fun x => by
      obtain ⟨d, hd⟩ := hs x
      exact ⟨_, hd, -d, by rw [Nat.cast_smul_eq_nsmul, smul_neg, add_neg_cancel_right]⟩)
    (q (0 + n • d₀))
    (fun t ht => ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      (mul_right_cancel ((h₁ t ht).trans (h₁ _ hd₀).symm))))
  rw [e, h0, LinearMap.zero_apply, add_zero]

theorem value_eq_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} {k : ℤ}
    {s s' : LB.Sec (LPow A L k T)} {r x y : Γ(T.left, ⊤)} (h : SecM.ofSec A s = r • SecM.ofSec A s') {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))}
    (H : IsValueAt A L k s w τ x) (H' : IsValueAt A L k s' w τ y) : x = r * y := by
  refine fn_ext fun z _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
  have a := sv_of_isValueAt H (𝟙 T) hJ
  have b := sv_of_isValueAt H' (𝟙 T) hJ
  have c : sv A s (lift (𝟙 T) (𝟙 T ≫ w)).left z J =
      gs (𝟙 T.left) z ⊤ r * sv A s' (lift (𝟙 T) (𝟙 T ≫ w)).left z J := by
    have := ThetaAct.sv_smul r (SecM.ofSec A s') (lift (𝟙 T) (𝟙 T ≫ w)).left z hJ
    rw [← h, lift_fst_left] at this
    exact this
  rw [a, b, ← _root_.mul_assoc] at c
  rw [gs_mul _ _ ⊤ trivial]
  exact (Units.mul_left_inj _).1 c

theorem levelPoint_injective {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Spec (CommRingCat.of K))} {M : ℕ}
    [NeZero M] {ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g) :
    Function.Injective (levelPoint lev hg) := by
  subst hg
  have E : ∀ c : Fin (2 * P.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  intro a b h
  have h₀ := lev.indep K (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
    ((E _).trans (h.trans (E _).symm))
  exact funext fun i => ZMod.val_injective M (congrArg Fin.val (congrFun h₀ i))

end GlobalTheory.TwoLevels

namespace GlobalTheory


open TwoLevels ThetaCoord in
theorem levelBasis_eq_of_isThetaPt : Out.Laws → ∀ (g n j N' : ℕ), Odd n → N' = n ^ j → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev lev' : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → Out.IsThetaPt P N' (levelPoint lev' hg) v → (∀ i, levelBasis lev hg i ^ N' = levelBasis lev' hg i ^ N') → (∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0) → ∀ i, levelBasis lev hg i = levelBasis lev' hg i := by
  intro hLaw g n j N' hn hN K _ _ P hg ze lev lev' v hv hv' hm hs
  have hG := hLaw.globalFns
  have := P.isAb.comm
  have ho : Odd N' := hv.1
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hp := levelBasis_pow lev hg
  have hp' := levelBasis_pow lev' hg
  have inj := levelPoint_injective lev hg
  choose s hs' using fun i => (pow_eq_one_iff (Nat.mul_one (N' ^ 2)).symm lev hg _).1 (hp' i)
  let σ := Fintype.linearCombination (ZMod (N' ^ 2)) s
  have e : ∀ a, levelPoint lev' hg a = levelPoint lev hg (σ a) := fun a => by
    rw [levelPoint_eq_lab, levelPoint_eq_lab]
    refine char_ext (lab (levelBasis lev' hg)) (fun a => lab (levelBasis lev hg) (σ a)) (lab_add hp')
      (fun a b => by rw [map_add (f := _), lab_add hp]) (fun i => ?_) a
    rw [lab_single hp', ← hs' i, pow_one, levelPoint_eq_lab, Fintype.linearCombination_apply_single, one_smul]
  have hw : ∀ (l : Out.Level P (N' ^ 2) ze) a b, Out.WeilIs P.A P.L (N' ^ 2 : ℕ) (levelPoint l hg a) (levelPoint l hg b)
      (ze ^ (labelSymp a b).val) := fun l a b => by
    rw [levelPoint_eq_lab]
    exact weilIs_lab hG P (levelBasis_pow l hg) (ze := ze) l.prim.pow_eq_one (weilIs_levelBasis l hg)
      (fun a b => ((hLaw.weil _ P _ _).1 _ _ (lab_pow (levelBasis_pow l hg) a)
        (lab_pow (levelBasis_pow l hg) b)).exists) a b
  have hσ : ∀ a b, labelSymp (σ a) (σ b) = labelSymp a b := fun a b => by
    have h := hw lev' a b
    rw [e, e] at h
    exact ZMod.val_injective _ (lev.prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      (CommutatorPairing.weilIs_unique hG P.isAb P.isLB (hw lev _ _) h))
  have hN' : ∀ a, N' • σ a = N' • a := fun a => inj (by
    have h := e a
    rw [levelPoint_eq_lab, levelPoint_eq_lab] at h
    rw [levelPoint_eq_lab, lab_nsmul hp, lab_nsmul hp, ← h]
    exact char_ext (fun a => lab (levelBasis lev' hg) a ^ N') (fun a => lab (levelBasis lev hg) a ^ N')
      (fun a b => by rw [lab_add hp', mul_pow]) (fun a b => by rw [lab_add hp, mul_pow])
      (fun i => by rw [lab_single hp', lab_single hp, hm]) a)
  have C := (theta_coordinates hLaw g N' 1 (N' ^ 2) N' rfl (Nat.one_mul _).symm).1 (Sp K) P hg ze
  obtain ⟨⟨th, t, hth, ht⟩, H⟩ := C lev v hv
  obtain ⟨H, hr⟩ := H th t hth ht
  have H' := ((C lev' v hv').2 th (fun a => t (σ a)) hth (by
    obtain ⟨s₁, α, U, hα, h₁, hU, h₂⟩ := ht
    exact ⟨s₁, α, fun a => U (σ a), hα, h₁, fun a => by beta_reduce; rw [e]; exact hU _, fun a => h₂ _⟩)).1 0
  replace H := H 0
  have z : ∀ l : Out.Level P (N' ^ 2) ze, levelPoint l hg 0 ^ N' = 1 := fun l => by
    rw [levelPoint_eq_lab, lab_zero, one_pow]
  rw [z] at H H'
  obtain ⟨τ, hτ⟩ := DVR.exists_gen_of_local P.L P.isLB (K := Fin 1)
    (fun _ => (1 : Out.baseOver (Sp K) ⟶ P.A).left) (fun _ => ((N' ^ 2 : ℕ) : ℤ))
  obtain ⟨u, hu⟩ := H τ hτ
  obtain ⟨u', hu'⟩ := H' τ hτ
  have z₁ : ∀ a : Fin (2 * g) → ZMod (N' ^ 2), thetaCoordExp N' 1 a 0 = 0 := fun a => by
    simp [thetaCoordExp, labelSymp]
  have z₂ : ∀ a : Fin (2 * g) → ZMod (N' ^ 2), thetaCoordIdx N' 1 a 0 = a := fun a => by
    simp [thetaCoordIdx]
  simp only [z₁, z₂, pow_zero, _root_.mul_one] at hu hu'
  have : IsDomain Γ((Out.baseOver (Sp K)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := eq_of_proportional (R := Γ((Out.baseOver (Sp K)).left, ⊤)) hn hN (ζ := ze) lev.prim σ hσ hN' v u u'
    (fun a => (value_eq_mul P.isLB (one_smul _ _).symm (hu (σ a)) (hu' a)).trans (_root_.one_mul _))
    (fun a b => (Units.mul_right_inj u).1
      ((value_eq_mul P.isLB (hr a b) (hu a) (hu _)).trans (mul_left_comm _ _ _))) hs
  intro i
  have h := e (Pi.single i 1)
  rw [key, levelPoint_eq_lab, levelPoint_eq_lab, lab_single hp', lab_single hp] at h
  exact h.symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplication
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGerm

theorem associated_gs_down {X Y Z : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
    (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) (r : Z ⟶ X) (z : Z) (j : PUnit → L.ι)
    (hj : r z ∈ LB.wchart L (fun _ : PUnit => 𝟙 X) j) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Associated (gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j))
      (sval b (r ≫ ρ) z J) := by
  have hle := (PowSec.chart_eq L σ ρ e j).le
  have h₁ : gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j) =
      gs (r ≫ ρ) z (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) (b.f (fun _ => j PUnit.unit)) :=
    (gs_res r z hle hj _).trans (gs_pull r ρ z _ (hle hj) _)
  rw [h₁, sec_trans b (r ≫ ρ) z (j := fun _ => j PUnit.unit) (hle hj) (hJ.mem (fun _ : Fin 1 => σ) (r ≫ ρ))]
  exact associated_unit_mul_left _ _ (Units.isUnit _)

theorem germ_origin : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  intro hLaw K _ _ P N m J x th t ρ e a hth H hx
  let π : P.A ⟶ Out.baseOver (Sp K) := Over.homMk P.A.hom (Category.comp_id _)
  let ρ' : P.A ⟶ Out.baseOver (Sp K) ⊗ P.A := lift π (𝟙 _)
  have ρ₂ : ρ'.left ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_snd _ _ : ρ' ≫ _ = _)
  have ρ₁ : ρ'.left ≫ (fst (Out.baseOver (Sp K)) P.A).left = P.A.hom :=
    congrArg (fun q => q.left) (lift_fst _ _ : ρ' ≫ _ = _)
  have ρ₃ : (snd (Out.baseOver (Sp K)) P.A).left ≫ ρ'.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain rfl : ρ = ρ'.left := by
    rw [← Category.comp_id ρ, ← ρ₃, ← Category.assoc, e, Category.id_comp]
  haveI : IsIso ρ'.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨?_, fun y k l hk hl => ?_⟩
  · by_contra hne
    push_neg at hne
    have hz : Out.SecM.ofSec P.A th = 0 := by
      refine Subtype.ext (funext fun j => ?_)
      obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
      exact PowSec.appLE_injective ρ'.left _ _
        (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ'.left ρ₂ (fun _ => k))
        ((hne fun _ => k).trans (map_zero _).symm)
    have : Subsingleton (Out.SecM P.A P.L (1 : ℕ) (Out.baseOver (Spec (CommRingCat.of K)))) :=
      subsingleton_of_forall_eq 0 fun y => by
        obtain ⟨r, hr⟩ := hth (Out.SecM.toSec P.A y)
        have e : y = r • Out.SecM.ofSec P.A th := Subtype.ext (funext hr)
        exact e.trans ((congrArg (r • ·) hz).trans (smul_zero r))
    have hnt : Nontrivial Γ((Out.baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    have := hLaw.globalSectionsRank K P 1 le_rfl
    rw [Module.finrank_zero_of_subsingleton, one_pow] at this
    exact zero_ne_one this
  · obtain ⟨s, α, U, -, hs, hU, ht⟩ := H
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ y)
    have hI' : Good P.L y I := hI
    have b₁ := ThetaCoord.sv_act ((hU a).pt_eq.trans hx) (ht a) π hI' (𝟙 _)
    have b₂ := ThetaCoord.sv_mulPull hs π hI' (𝟙 _)
    rw [MonObj.comp_one, _root_.one_mul, b₂] at b₁
    have e₁ : (Out.mulA P.A m).left ≫ ρ'.left = (lift π (𝟙 P.A ^ m)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id]
      congr 2
      exact Over.OverMorphism.ext (Over.w (Out.mulA P.A m))
    have a₁ := associated_gs_down P.L _ _ e (N : ℤ) (t a) (𝟙 _) y k hk hI'
    have a₂ := associated_gs_down P.L _ _ e ((1 : ℕ) : ℤ) th (Out.mulA P.A m).left y l hl hI'
    rw [Category.id_comp] at a₁
    rw [e₁] at a₂
    refine a₁.trans (Associated.trans ?_ a₂.symm)
    exact (Associated.of_eq b₁).trans ((associated_unit_mul_left _ _ (Units.isUnit _)).trans
      (associated_unit_mul_left _ _ (Units.isUnit _)))

end GlobalTheory.ThetaGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCoset
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSupport


open Out in
theorem isValueAt_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (hL : L.IsLB) {n : ℤ}
    {s : LB.Sec (LPow A L n T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n))}
    (hτ : τ.IsGen) {c c' : Γ(T.left, ⊤)} (h : IsValueAt A L n s w τ c) (h' : IsValueAt A L n s w τ c') : c = c' :=
  (EvVal.existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover L hL _ _)
    (EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A w).left
      (fun _ => w.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le A L w) s) τ hτ).unique h h'


open ThetaCoord in
theorem exists_ne_zero_in_coset : Out.Laws → ∀ (g n N' : ℕ), 2 ≤ n → n ^ 2 ∣ N' → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → ∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0 := by
  intro hLaw g n N' hn hdvd K _ _ P hg ze lev v hv c
  obtain ⟨k, hk⟩ := hdvd
  have ho := hv.1
  have hu := hv.2.1
  have := P.isAb.comm
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hK : (N' : K) ≠ 0 := by
    have := hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hnK : (n : K) ≠ 0 := fun h => hK (by rw [hk]; push_cast; rw [h]; ring)
  obtain ⟨H₁, H₂⟩ := theta_coordinates hLaw g 1 N' 1 N' (by norm_num) (by norm_num)
  obtain ⟨⟨th, t, hth, ht⟩, Hv⟩ := H₁ (Sp K) P hg ze lev v hv
  obtain ⟨-, hli, -⟩ := (H₂ K ho hK P hg ze lev).2.2 th t hth ht
  haveI : Nontrivial Γ((Out.baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  have h0 : Out.SecM.ofSec P.A (t 0) ≠ 0 := by
    have := hli.ne_zero (fun _ => 0)
    have e : (fun _ : Fin (2 * g) => (((0 : Fin 1) : ℕ) : ZMod (N' ^ 2))) = 0 := funext fun _ => by simp
    simpa only [e] using this
  obtain ⟨x, hx, τ, w, hτ, hw, hw0⟩ := hLaw.goodPt K P n hn hnK (t 0) h0 (levelPoint lev hg c ^ N')
  obtain ⟨d, rfl⟩ := (pow_eq_one_iff (M := N' ^ 2) (d := n) (e := (n * k) * N')
    (by rw [sq]; nth_rewrite 1 [hk]; ring) lev hg x).1 hx
  have e : levelPoint lev hg c ^ N' * levelPoint lev hg d ^ (n * k * N') =
      levelPoint lev hg (c + n • k • d) ^ N' := by
    rw [levelPoint_eq_lab, ← mul_smul, lab_add (levelBasis_pow lev hg), lab_nsmul (levelBasis_pow lev hg), mul_pow,
      ← pow_mul]
  refine ⟨k • d, fun hz => hw0 ?_⟩
  have key := ((Hv th t hth ht).1 (c + n • k • d))
  rw [← e] at key
  obtain ⟨u, hu'⟩ := key τ hτ
  have h₁ := hu' 0
  have e₂ : thetaCoordIdx 1 N' 0 (c + n • k • d) = c + n • k • d := by
    simp [thetaCoordIdx]
  rw [e₂, hz, mul_zero] at h₁
  exact isValueAt_unique P.isLB hτ hw h₁

end GlobalTheory.ThetaSupport
end
end

