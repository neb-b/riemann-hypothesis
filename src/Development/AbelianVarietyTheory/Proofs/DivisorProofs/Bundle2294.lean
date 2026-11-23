module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvTEqTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrincSubring

section Transport

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {Z : Scheme.{0}} (f : Z ⟶ X')
    (z : Z) {k : L'.ι} (hk : f z ∈ L'.U k) : gm f z (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (f z))
  have e := hw Z f z j j k k hj hj hk hk
  rw [gm_self hL (f ≫ F) z hj, _root_.one_mul] at e
  exact inv_eq_one.1 (mul_eq_right.1 e.symm)

theorem trF_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {q : K → L'.ι} (hq : r z ∈ LB.wchart L' φ' q) :
    trF (L := L') φ' ε r z q q = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self_of_pGen hw hL (r ≫ φ' k) z (Set.mem_iInter.1 hq k), one_zpow]

theorem exists_down_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self_of_pGen hw hL _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

end Transport

theorem kerAlong_of_pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  intro S S' f A _ P A₁ _ P₁ φ φ₂ hP₁ h hs hw hK T a ha x hx
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨c, hc⟩ := hx
  let T' : Over S' := Over.mk a
  have hxw : x.left ≫ A₁.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : T' ⟶ A := Over.homMk (h.1.lift x.left a hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = x.left := h.1.lift_fst _ _ _
  have key : x' = 1 := hK T' x' <| by
    let b : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ T := Over.homMk (fst T' A).left (by
      show (fst T' A).left ≫ T.hom = (T' ⊗ A).hom ≫ f
      rw [← ha, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (fst T' A)))
    let c' : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ A₁ := pushPt h.1.w (snd T' A)
    have k₁ : (lift b c').left ≫ (fst T A₁).left = (fst T' A).left := congrArg (fun q => q.left) (lift_fst b c')
    have k₂ : (lift b c').left ≫ (snd T A₁).left = (snd T' A).left ≫ φ := congrArg (fun q => q.left) (lift_snd b c')
    have k₃ : (fst T' A ≫ x').left ≫ φ = (lift b c').left ≫ (fst T A₁ ≫ x).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc, k₁]
    have k₄ := GlobalTheory.SiegelDescent.lift_comp_square hs (T' := T' ⊗ A) (lift b c').left _ _ _ _ k₃ k₂.symm
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame P₁
      (fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left ≫ φ₂) _ _ (lift b c').left fun _ => k₄) c hc
    exact exists_down_of_pGen (φ' := fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left) (ε := fun _ => 1)
      ((isGen_iff w).1 hwg) hP₁ c₂ h₂
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) (by
    show 𝟙 T.left ≫ T.hom = a ≫ f
    rw [Category.id_comp, ha])
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext (by
    show 𝟙 T.left ≫ x.left = x'.left ≫ φ
    rw [Category.id_comp, hx'])
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A₁) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  have e₃ : 𝟙 T.left ≫ x.left = 𝟙 T.left ≫ (1 : T ⟶ A₁).left := congrArg (fun q => q.left) e₂
  exact Over.OverMorphism.ext (by simpa only [Category.id_comp] using e₃)

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral GlobalTheory.KTrivSpread

noncomputable section

namespace GlobalTheory.PrincSubring

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}
variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)
variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)


include hadd hsym hLW hmon huniv in
theorem trivAlong_of_kernelAlong {S' : Scheme.{0}} (g : S' ⟶ S) (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A,
      pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : TrivAlong G L g := by
  intro T a ha x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv T fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    (T.left.openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 :=
    (hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e


include hadd hsym hLW hmon huniv in
theorem kernelAlong_of_trivAlong {S' : Scheme.{0}} (g : S' ⟶ S) (u₀ : Fin n) (hK : TrivAlong G L g)
    (T : Over S) (a : T.left ⟶ S') (ha : a ≫ g = T.hom) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  obtain ⟨y, hy, -⟩ := huniv T fun u => if u = u₀ then x else 1
  have hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0 := fun Z b z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z b).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK T a ha y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have h := hy u₀
  rw [if_pos rfl, h1, MonObj.one_comp] at h
  exact h.symm

end Calc

theorem kerAlong_iff_trivAlong : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}}
    (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  intro S h A _ _ P hs hA S' g
  obtain ⟨hab, -, hP, hr₁, hr₂, hsw⟩ := hs
  have hadd : ∀ (T : Over S) (x x' y : T ⟶ A),
      pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A
      (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    unfold PrincipalIntegral.pair
    abel
  have hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x := fun T x y => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsw
    have k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    unfold PrincipalIntegral.pair
    rw [← k, pull_comp, ← e]
  obtain ⟨-, hdet⟩ := isE8_W8
  have hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u :=
    fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP _ _
  have hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A) := cls_linComb hP _ _ _
  have tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x) :=
    fun T x => by
      rw [PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)
  constructor
  · intro hk
    exact trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)
  · intro hK T a ha x hx
    exact kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.ArchProof

theorem coset_series {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 1 ≤ m) (y : X) (A B : X → ℂ)
    (h1 : ∀ χ, A (y + m • χ) = B χ) (h0 : ∀ α, (∀ χ, α ≠ y + m • χ) → A α = 0) (hB : Summable fun χ => ‖B χ‖) :
    (Summable fun α => ‖A α‖) ∧ ∑' α, A α = ∑' χ, B χ := by
  have hi : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have e : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using add_left_cancel h
    exact smul_right_injective X (by omega : (m : ℤ) ≠ 0) e
  have hz : ∀ α ∉ Set.range fun χ : X => y + m • χ, A α = 0 := fun α hα => h0 α fun χ e => hα ⟨χ, e.symm⟩
  refine ⟨(hi.summable_iff (f := fun α => ‖A α‖) fun α hα => by rw [hz α hα, norm_zero]).1 ?_, ?_⟩
  · simpa only [Function.comp_def, h1] using hB
  · rw [← hi.tsum_eq (f := A) fun α hα => by_contra fun h => hα (hz α h)]
    simp only [h1]

theorem exists_log (T : ℝ) (u : ℂ) (hu : u ≠ 0) (h : ‖u‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) = u := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (Complex.log u / (2 * Real.pi * Complex.I))) = u := by
    rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]
  refine ⟨_, ?_, e⟩
  rw [← e, Complex.norm_exp, Real.exp_lt_exp] at h
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at h ⊢
  have : ((2 * Real.pi * Complex.I : ℂ) * w).re = -(2 * Real.pi * w.im) := by simp
  rw [this] at h
  have := Real.pi_pos
  nlinarith

theorem exists_cd (κ : Rule) (hκ : Rule4 κ) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {r : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) :
    ∃ (d : CD N D.P.g r bX) (_ : Geo ν d.toAB), KeyOK κ ν d.toAB := by
  have : ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
    rcases Nat.eq_zero_or_pos D.P.g with h | h
    · exact GlobalTheory.MBLow.DimZero.main κ R D h1 h2 N ν h
    · exact _root_.GlobalTheory.MBLow.AbCl.exists_ab_keyOK κ hκ R D h1 h2 N ν h
  obtain ⟨e, G, hK⟩ := this
  obtain ⟨d, rfl⟩ := GlobalTheory.MBLow.Cl.PsiFrame.exists_cd N D.P.g r bX e (GlobalTheory.MBLow.Cl.cub_of_geo R D h1 h2 N ν _ e ⟨G⟩) (GlobalTheory.MBLow.Cl.sym_of_geo R D h1 h2 N ν _ e ⟨G⟩)
  exact ⟨d, G, hK⟩

theorem exists_vec (κ : Rule) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {g r : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N D.P.g r bX) (G : Geo ν d.toAB) (hK : KeyOK κ ν d.toAB)
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R ℂ))
    (hA : Adapted ν vB bX σ gm) (k₀ : ℂ) (hk : BKey κ ν vB k₀) :
    ∃ (Mx : Matrix (Fin g) (Fin g) ℂ) (c₀ : Fin g → ℂ), Mx.det ≠ 0 ∧ k₀ * d.c ^ 8 = Mx.det ^ 4 ∧
      ∀ j (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F →
        (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) →
        (jc ν s (gm j) α).fst / ν.rg ^ k = F 0 ∧ (jc ν s (gm j) α).snd / ν.rg ^ k =
          fderiv ℂ F 0 ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) + k * c₀ j * F 0 := by
  obtain ⟨hb, ho, hl, hr⟩ := hA
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hW : ∀ j, ∃ W, IsD ν d.toAB W (gm j).b ∧ ∀ l, j = σ.symm (Sum.inr l) → W = 0 := by
    intro j
    by_cases h : ∃ l, j = σ.symm (Sum.inr l)
    · obtain ⟨l, rfl⟩ := h
      exact ⟨0, by rw [(hr l).1]; exact GlobalTheory.MBLow.Cl.DZero.isD_zero R D h1 h2 N ν _ d.toAB, fun _ _ => rfl⟩
    · obtain ⟨o, hz, hp⟩ := ho j
      obtain ⟨W, hW⟩ := G.dif (gm j).b (hp.1.symm.trans (congrArg (·.left) hz.1))
      exact ⟨W, hW, fun l e => absurd ⟨l, e⟩ h⟩
  choose W hW hW0 using hW
  choose Z c₀ hZ hT hJ using fun j => GlobalTheory.MBLow.Cl.jet_family_deriv R D h1 h2 N ν _ r g bX d σ G (gm j) (W j) (ho j) (hW j)
  have hs : ∀ {n : ℕ} (v : Fin n → ℂ), (2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • v = v :=
    fun v => inv_smul_smul₀ hne v
  let Mx : Matrix (Fin g) (Fin g) ℂ := fun j => (2 * Real.pi * Complex.I : ℂ) • Z j
  let MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := fun i => (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))
  have hdet : Mx.det = MB.det := by
    refine GlobalTheory.MBLow.Cl.det_eq_det_block _ r g σ Mx MB (fun i => ?_) fun l => ⟨?_, ?_⟩
    · exact congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) (hZ (σ.symm (Sum.inl i)))
    · have := congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) ((hZ (σ.symm (Sum.inr l))).trans (hW0 _ l rfl))
      simp only [smul_zero] at this
      exact this
    · funext l'
      have e := congrArg TrivSqZeroExt.snd (((hT _ (hW0 _ l rfl) (bX l')).symm).trans ((hr l).2 (bX l')))
      have hc : co bX (bX l') = Pi.single l' 1 := by
        funext i
        by_cases hi : i = l' <;> simp [co, hi, Finsupp.single_apply, eq_comm]
      rw [hc, single_one_dotProduct] at e
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add, Module.Basis.repr_self] at e
      refine e.trans ?_
      by_cases hi : l' = l <;> simp [hi, Finsupp.single_apply]
  obtain ⟨hd, hv⟩ := hK vB (fun i => (gm (σ.symm (Sum.inl i))).b) MB k₀ hb hl (fun i => by
    change IsD ν d.toAB ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))) _
    rw [hs]; exact hW _) hk
  refine ⟨Mx, c₀, hdet ▸ hd, hdet ▸ hv, fun j k s f α F hs' hF hY => ?_⟩
  have : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j = Z j := hs _
  rw [this]
  exact hJ j k s f α F hs' hF hY

theorem arch_of_rule4 : ∀ κ : Rule, Rule4 κ → Arch κ := by
  intro κ hκ R _ _ _ _ D h1 h2 _ N ν g r m k hg hm hmk β ζ q hq s hs vB bX σ gm hA k₀ hk
  have hm1 : 1 ≤ m := hm.pos
  obtain ⟨d, G, hK⟩ := exists_cd κ hκ h1 h2 ν bX
  obtain ⟨Mx, c₀, hdet, hval, hJ⟩ := exists_vec κ h1 h2 ν d G hK vB σ gm hA k₀ hk
  obtain ⟨M, Nn, hrep, hlab⟩ := GlobalTheory.MBLow.Cl.exists_integral_labels N _ r g bX d σ (m ^ 2) (by positivity) ζ q hq
  obtain ⟨T, hT⟩ := GlobalTheory.MBLow.Cl.BlockPos.full_posDef N _ r g bX d σ k β
  obtain ⟨hdiff, htw⟩ := GlobalTheory.MBLow.Cl.term_smul_bmat N _ r g bX d σ
  refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun u hu0 hu => ?_⟩
  obtain ⟨w, hw, hwu⟩ := exists_log T u hu0 hu
  obtain ⟨hS, hsym, hpos⟩ := hT w hw
  set S := w • bmat bX β with hSdef
  set V : Fin g → Fin g → ℂ := fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j with hV
  have key : ∀ a j,
      ((Summable fun α => ‖(jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) ∧
      (Summable fun α => ‖(jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a)) 0 (V j) +
            ((m ^ 2 : ℕ) * c₀ j) * (d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) := by
    intro a j
    obtain ⟨f, hf, hf1, hf0⟩ := hs a
    rw [(hrep a).1] at hf1 hf0
    set y := ∑ l, tP σ (Nn a) l • bX l with hy
    obtain ⟨s1, s2, t1, t2⟩ := GlobalTheory.MBLow.Cl.term_sum_and_fderiv N _ r g bX d σ S hS hpos m (M a) (Nn a) (V j)
    have on : ∀ χ, _ := fun χ => hJ j _ (s a) f (y + m • χ) (fun Y => d.c * d.term σ 0 m (M a) (Nn a) χ Y) hf
      ((hdiff _ _ _ _ _).const_mul _) fun Y h hY => by
        rw [hf1, GlobalTheory.MBLow.Cl.evT_eq_term N _ r g bX d σ m hm (M a) (Nn a) (q a) (hrep a) Y h hY χ]; ring
    have off : ∀ α, (∀ χ, α ≠ y + m • χ) → _ := fun α hα => hJ j _ (s a) f α (fun _ => 0) hf
      (differentiable_const _) fun Y h hY => by rw [hf0 α hα]; simp
    have tw : ∀ χ, d.term σ S m (M a) (Nn a) χ = fun Z => d.term σ 0 m (M a) (Nn a) χ Z *
        u ^ (β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat := fun χ => funext fun Z => by
      rw [← hwu]; exact htw k m β hm1 hmk w (M a) (Nn a) χ Z
    have A := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * d.term σ S m (M a) (Nn a) χ 0)
      (fun χ => by simp only [(on χ).1, tw χ]; ring) (fun α hα => by simp only [(off α hα).1, zero_mul])
      (by simpa only [norm_mul] using s1.mul_left ‖d.c‖)
    have B := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * fderiv ℂ (d.term σ S m (M a) (Nn a) χ) 0 (V j) +
        ((m ^ 2 : ℕ) * c₀ j) * (d.c * d.term σ S m (M a) (Nn a) χ 0))
      (fun χ => by
        simp only [(on χ).2, tw χ]
        rw [fderiv_const_mul (hdiff _ _ _ _ _ _), fderiv_mul_const (hdiff _ _ _ _ _ _)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hV]
        ring)
      (fun α hα => by simp [(off α hα).2])
      (((s2.of_norm.mul_left d.c).add ((s1.of_norm.mul_left d.c).mul_left _)).norm)
    refine ⟨⟨A.1, ?_⟩, B.1, ?_⟩
    · rw [A.2, tsum_mul_left, t1]
    · rw [B.2, (s2.of_norm.mul_left d.c).tsum_add ((s1.of_norm.mul_left d.c).mul_left _), tsum_mul_left, tsum_mul_left,
        tsum_mul_left, t1, t2]
  have hrg : ν.rg ^ (m ^ 2) ≠ 0 := pow_ne_zero _ (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hmul : ∀ (x v : N.X → ℂ), (Summable fun α => ‖x α / ν.rg ^ (m ^ 2) * v α‖) → Summable fun α => ‖x α * v α‖ := by
    intro x v h
    refine (h.mul_left ‖ν.rg ^ (m ^ 2)‖).congr fun α => ?_
    rw [← norm_mul, ← _root_.mul_assoc, mul_div_cancel₀ _ hrg]
  refine ⟨fun a j => ⟨hmul _ _ (key a j).1.1, hmul _ _ (key a j).2.1⟩, ?_⟩
  have ha : Half (d.aF σ) := fun i => by
    unfold CD.aF
    rcases σ i with i | i
    · exact d.ha i
    · exact Or.inl rfl
  have hb : Half (d.bF σ) := fun i => by
    unfold CD.bF
    rcases σ i with i | i
    · exact d.hb i
    · exact d.hb2 i
  obtain ⟨x₀, hg₀, U, hNF⟩ := GlobalTheory.MBLow.Cl.exists_keyIn_nf g (d.full σ S) (d.aF σ) (d.bF σ) d.c Mx hg hsym hpos ha hb d.hc hdet
  obtain ⟨lev, hlev⟩ := GlobalTheory.MBLow.LabelLevel.exists_level_of_labels g x₀ hg₀ U _ _ _ _ _ hNF (m ^ 2) (by positivity) ζ hq.1 M Nn hlab
  refine ⟨x₀, hg₀, lev, fun a => d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0,
    fun a j => (key a j).1.2.symm, ?_, ?_⟩
  · simp only [fun a j => (key a j).2.2]
    exact GlobalTheory.MBLow.Cl.thJet_of_normalForm g x₀ hg₀ U _ _ _ _ _ hNF m hm _ M Nn _ (fun a => by rw [hlev a, Nat.cast_pow]) _
  · exact mul_right_cancel₀ (pow_ne_zero 8 d.hc) ((GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 g x₀ hg₀ U _ _ _ _ Mx hNF).2.trans hval.symm)

end GlobalTheory.MBLow.ArchProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (N : LB (A ⊗ T).left), Fam A N → Triv (abelian₂ (GlobalTheory.TwistFlat.bc A φ) (GlobalTheory.TwistFlat.twist A φ N)) := by
  first | exact @GlobalTheory.TwistFlat.triv_lam_twist | exact GlobalTheory.TwistFlat.triv_lam_twist | (intros; apply GlobalTheory.TwistFlat.triv_lam_twist <;> assumption)
end

