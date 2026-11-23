module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TripleExt

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) : (cubeLB G x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls_pre {T T' : Over S} (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull u.left (cubeCls x c) = cubeCls (fun i => u ≫ x i) c := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z => _ • pull (CommaMorphism.left z) c) (psum_hom (preHom u) x I.down)

theorem pull_cubeCls_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = u ≫ x i)
    (c : Pic G.left) : pull (Y := T'.left) u.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x u hx]

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : pull (eSec G) c = 0) :
    cubeCls (fun _ : Fin n => η[G]) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e : psum G (fun _ : Fin n => η[G]) I.down = η[G] := by
    have := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ : Fin n => η[G]) I.down
    simp only [MonoidHom.one_apply, e₁] at this
    exact this.symm
  rw [e]
  exact (congrArg _ hc).trans (smul_zero _)

end Cube

theorem pic_ext (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) {U H HU : Scheme.{0}}
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (hp : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hj : IsPullback jH pU p j) (α β : Pic H)
    (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) : α = β := by
  obtain ⟨A, hA, rfl⟩ := cls_surj α
  obtain ⟨B, hB, rfl⟩ := cls_surj β
  exact (cls_eq_iff hA hB).2 ((_root_.GlobalTheory.lbIso_extend_of_normal S hS U H HU j p e jH pU hp hg he hj A B hA hB
    ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₁)).1 ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₂))

theorem exists_sab_extension : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (NumberField.RingOfIntegers E) G) (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left), IsGrpPullback t₀.G G j a → (∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) → ∀ M : LB G.left, M.IsLB → LBIso (M.pull a) t₀.PP.L → ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  intro S _ _ hS E _ _ _ H U _ j _ G _ _ semi act t₀ a h hact M hM hMa
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨PP, cub, m, rfl, hme, hlin, hsym⟩ := _root_.GlobalTheory.NormalCubeExt.exists_cubical_extension S hS U j G t₀.G a h t₀.PP t₀.cub M hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull m.F (cls PP.L PP.isLB) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  refine ⟨PP, cub, hsym t₀.sym, fun b => ?_, ?_, ⟨m, h, hme, hact, hlin⟩, rfl⟩
  · refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    have hsm : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have hgc : GeometricallyConnected (G ⊗ G).hom := by
      show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
      exact GeometricallyConnected.comp _ _
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ y := fun y =>
      ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
    obtain ⟨y₁, hy₁⟩ := hy (fst G G)
    obtain ⟨y₂, hy₂⟩ := hy (snd G G)
    let e : 𝟙_ (Over S) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext S hS j (G ⊗ G).hom e.left u.left T'.hom hsm
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  · refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext S hS j G.hom (eSec G) m.F t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = m.F := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]

end GlobalTheory.TripleExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.SquareLevel

open GlobalTheory.ThetaCoord

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem labelSymp_eq (g M : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) :
    labelSymp (a ∘ (halves g).symm) (b ∘ (halves g).symm) = eStd g M a b := by
  have h₁ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inl, if_neg (by omega), if_neg (by omega)]
  have h₂ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₃ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_neg (by omega), if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₄ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inr, halves_inr, if_neg (by omega), if_neg (by omega)]
  rw [labelSymp, ← (halves g).sum_comp]
  simp_rw [← (halves g).sum_comp]
  simp [Fintype.sum_sum_type, h₁, h₂, h₃, h₄, eStd, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {S : Scheme.{0}}

theorem linComb_pow_left {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb (fun i => y i ^ M) c = linComb y (fun i => M * c i) := by
  simp only [linComb, pow_mul]

theorem linComb_pow_right {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb y c ^ M = linComb y (fun i => M * c i) := by
  simp only [linComb, List.prod_ofFn, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem comp_linComb {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : h ≫ linComb y c = linComb (fun i => h ≫ y i) c := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) (fun a b => MonObj.comp_mul _ _ _)
  simp only [linComb, List.prod_ofFn]
  exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)

theorem existsUnique_lab {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ} [NeZero M]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ (M ^ 2) = 1)
    (ind : ∀ c c' : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c')
    (z : T ⟶ A) (hz : z ^ M = 1) (sp : ∃ c : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = z) :
    ∃! a : Fin n → ZMod M, lab (fun i => y i ^ M) a = z := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have lt : ∀ a : ZMod M, M * a.val < M ^ 2 := fun a => by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hM
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_
  · obtain ⟨c, hc⟩ := sp
    have h₀ := ind (fun i => ⟨(M * c i) % M ^ 2, Nat.mod_lt _ (pow_pos hM 2)⟩) (fun _ => ⟨0, pow_pos hM 2⟩) (by
      have e : linComb y (fun i => (M * c i) % M ^ 2) = linComb y (fun i => M * c i) := by
        simp only [linComb]
        exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (hy i)).symm)
      refine e.trans ?_
      rw [← linComb_pow_right, hc, hz]
      simp [linComb])
    have h₁ : ∀ i, M ∣ (c i : ℕ) := fun i => by
      have q : (M * c i) % M ^ 2 = 0 := congrArg Fin.val (congrFun h₀ i)
      exact Nat.dvd_of_mul_dvd_mul_left hM (sq M ▸ Nat.dvd_of_mod_eq_zero q)
    refine ⟨fun i => ((c i : ℕ) / M : ℕ), (linComb_pow_left _ _ _).trans
      ((congrArg (linComb y) (funext fun i => ?_)).trans hc)⟩
    rw [ZMod.val_cast_of_lt (Nat.div_lt_of_lt_mul (sq M ▸ (c i).2)), Nat.mul_div_cancel' (h₁ i)]
  · have h := ind (fun i => ⟨_, lt (a i)⟩) (fun i => ⟨_, lt (b i)⟩)
      ((linComb_pow_left _ _ _).symm.trans ((ha.trans hb.symm).trans (linComb_pow_left _ _ _)))
    funext i
    exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left hM (congrArg Fin.val (congrFun h i)))

theorem weilIs_pow_pow (hW : WeilSt) [IsLocallyNoetherian S] (P : PolAV S) {M : ℕ} {T : Over S}
    (hu : IsUnit (M : Γ(T.left, ⊤))) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hM : 1 ≤ M) (hx : x ^ (M ^ 2) = 1)
    (hy : y ^ (M ^ 2) = 1) (H : WeilIs P.A P.L (M ^ 2 : ℕ) x y c) :
    WeilIs P.A P.L M (x ^ M) (y ^ M) (c ^ M) := by
  have H' := CommPairing.weilIs_symm P.isLB H
  have k : ∀ n, WeilIs P.A P.L (M ^ 2 : ℕ) (y ^ (n + 1)) x (c⁻¹ ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using H'
    | succ n ih => rw [pow_succ y, pow_succ c⁻¹]; exact (hW S P _ T).2.1 _ _ _ _ _ ih H'
  have k' := CommPairing.weilIs_symm P.isLB (k (M - 1))
  rw [Nat.sub_add_cancel hM, inv_pow, inv_inv] at k'
  refine ((hW S P M T).2.2.2 M x _ _ (by rw [Nat.cast_mul]; exact hu.mul hu) (by rw [← sq, hx])
    (by rw [← pow_mul, ← sq, hy])).1 ?_
  rwa [← Nat.cast_mul, ← sq]

end GlobalTheory.SquareLevel

namespace GlobalTheory


open SquareLevel ThetaCoord in
theorem exists_torsionPoints_of_squareLevel : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  intro hL S _ P M ze hM hu lev
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  refine ⟨fun a => lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm), fun a b => lab_add hq _ _,
    fun K _ _ x z hz => ?_, fun a b => ?_, fun a => ?_, fun i i₁ i₂ h₁ h₂ => ?_⟩
  · have H := existsUnique_lab (M := M)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ lev.pt i)
      (fun i => by rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]) (lev.indep K x) z hz
      (lev.span K x z (by rw [sq, pow_mul, hz, one_pow]))
    refine ((Equiv.arrowCongr (halves P.g) (Equiv.refl (ZMod M))).existsUnique_congr fun a => ?_).2 H
    rw [lab, comp_linComb]
    simp only [MonObj.comp_pow]
    rfl
  · have hze : (ze ^ M) ^ M = 1 := by rw [← pow_mul, ← sq, lev.prim.pow_eq_one]
    have := weilIs_lab hL.globalFns P (T := baseOver S) hq (ze := ze ^ M) hze (fun i j => by
      have := weilIs_pow_pow hL.weil P (T := baseOver S) hu hM (lev.torsion i) (lev.torsion j) (lev.pairing i j)
      convert this using 1
      show (ze ^ M) ^ stdSymp P.g i j = (ze ^ stdSymp P.g i j) ^ M
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm])
      (fun a b => ((hL.weil S P M _).1 _ _ (lab_pow hq a) (lab_pow hq b)).exists)
      (a ∘ (halves P.g).symm) (b ∘ (halves P.g).symm)
    rw [labelSymp_eq] at this
    rw [pow_mul]
    exact this
  · refine ⟨linComb lev.pt fun i => (a ((halves P.g).symm i)).val, ?_, ?_⟩
    · simp only [linComb, List.prod_ofFn, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]
    exact (linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm
  · have k : ∀ s, lab (fun i => lev.pt i ^ M) ((Pi.single s (1 : ZMod M) : _ → ZMod M) ∘ (halves P.g).symm) =
        lev.pt (halves P.g s) ^ M := fun s => by
      rw [← lab_single (M := M) hq (halves P.g s)]
      congr 1
      funext j
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    have e₁ : i₁ = halves P.g (.inl i) := Fin.ext h₁
    have e₂ : i₂ = halves P.g (.inr i) := Fin.ext (h₂.trans (Nat.add_comm _ _))
    rw [e₁, e₂]
    exact ⟨k _, k _⟩

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwoGoodSectionsNearClosedPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.TwoSections

theorem exists_torsion_pair (M : Type) [CommGroup M] (P : M → Prop) (n : ℕ) (x : M)
    (h : ∀ c : M, 6 * Nat.card {h : M // h ^ n = 1 ∧ ¬ P (c * h)} < Nat.card {h : M // h ^ n = 1}) :
    ∃ b c : M, b ^ n = 1 ∧ c ^ n = 1 ∧ P b ∧ P c ∧ P (b * c) ∧ P (x * b) ∧ P (x * c) ∧ P (x * b * c) := by
  let H : Subgroup M := (powMonoidHom n : M →* M).ker
  have hH : Nat.card H = Nat.card {h : M // h ^ n = 1} := rfl
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by have := h 1; omega)
  have hB : ∀ c : M, 6 * Nat.card {h : H | ¬ P (c * h)} < Nat.card H := fun c => by
    have e : {h : H | ¬ P (c * h)} ≃ {h : M // h ^ n = 1 ∧ ¬ P (c * h)} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun h : M => h ^ n = 1) (fun h => ¬ P (c * h))
    rw [Nat.card_congr e, hH]
    exact h c
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_pair_avoiding_small_sets H _ _ (hB 1) (hB x)
  simp only [Set.mem_ofPred_eq, not_not, _root_.one_mul, Subgroup.coe_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨b, c, b.2, c.2, h1, h2, h3, h4, h5, by rwa [_root_.mul_assoc]⟩

theorem exists_pushHom {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (q : X ⟶ S') (s : X ⟶ S) (e : q ≫ f = s) :
    ∃ ρ : (Over.mk q ⟶ G') →* (Over.mk s ⟶ G), ∀ c, (ρ c).left = c.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk q), fun _ => rfl⟩

theorem exists_residue_point (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (w : X)
    (hw : IsClosed ({w} : Set X)) : ∃ (p : ℕ) (_ : Fact p.Prime) (x : Sp (kb p) ⟶ X), ∀ s, x s = w := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int X π).2.1 w hw
  obtain ⟨p, hp⟩ := CharP.exists (X.residueField w)
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime (X.residueField w) p⟩
  have : CharP (kb p) p := charP_kb
  have : IsAlgClosed (kb p) := isAlgClosed_kb
  letI : Algebra (ZMod p) (X.residueField w) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) (X.residueField w) := Module.Finite.of_finite
  let r : X.residueField w →+* kb p := (IsAlgClosed.lift (R := ZMod p) (S := X.residueField w) (M := kb p)).toRingHom
  refine ⟨p, hpp, Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w, fun s => ?_⟩
  have : (Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w) s ∈ Set.range (X.fromSpecResidueField w) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [Scheme.range_fromSpecResidueField] at this

end GlobalTheory.ZJ.TwoSections

namespace GlobalTheory.ZJ
open TwoSections

theorem Core.Law.six_of_few : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  intro hext C L T n hT hB hS hF w hw
  letI := L.grp
  letI := L.comm
  have := C.lft
  have := C.flat
  have hlft : LocallyOfFiniteType C.GG.hom := (GlobalTheory.ZJ.core_basic C).2.1
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨p, hp, x, hx⟩ := @exists_residue_point C.G.toScheme (C.GG.hom ≫ C.π) hlft' w hw
  obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
  obtain ⟨y, hy, hyU⟩ := hlift (x ≫ C.GG.hom)
  obtain ⟨τ⟩ := hT p y hyU
  obtain ⟨E⟩ := _root_.GlobalTheory.ZJ.Core.Theta.nonempty_ext hext C T p y τ fun p _ y τ => (L.test p y τ).1
  let s₀ : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hs : ∀ s : Sp (kb p), s = s₀ := fun s => Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  have hr : rPt p s₀ = cPt p := IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hz : y (cPt p) = (x ≫ C.GG.hom) s₀ := by rw [← hy, Scheme.Hom.comp_apply, hr]
  obtain ⟨N, hN, hsec⟩ := hS _ (hcl (x ≫ C.GG.hom) s₀)
  have hrange : Set.range (x ≫ C.GG.hom) ⊆ Set.range N.ι := by
    rintro _ ⟨s, rfl⟩
    rw [hs s, Scheme.Opens.range_ι]
    exact hN
  let t : Sp (kb p) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (x ≫ C.GG.hom) hrange
  have ht : t ≫ N.ι = x ≫ C.GG.hom := IsOpenImmersion.lift_fac _ _ _
  have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = t ≫ N.ι := by rw [Category.assoc, τ.fac, hy, ht]
  have hpb := (L.test p y τ).1
  let c₀ : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H :=
    Over.homMk (hpb.lift x (rPt p ≫ spMap τ.j) (ht.symm.trans e.symm)) (hpb.lift_snd _ _ _)
  have hc₀ : c₀.left ≫ τ.f = x := hpb.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := exists_pushHom (L.test p y τ) _ _ e
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := exists_torsion_pair (Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H)
    (fun c => ⊤ ≤ c.left ⁻¹ᵁ Out.nonzeroLocus E.θ) n c₀ (hF p y τ E)
  obtain ⟨b₁, hb₁, hb₂⟩ := hsec p y τ t b hz (ht.trans hy.symm) hb
  obtain ⟨c₁, hc₁, hc₂⟩ := hsec p y τ t c hz (ht.trans hy.symm) hc
  have key : ∀ d : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H, ⊤ ≤ d.left ⁻¹ᵁ Out.nonzeroLocus E.θ →
      Set.range (ρ d).left ⊆ T.Om L := by
    rintro d hd _ ⟨s, rfl⟩
    have := τ.j_loc
    have h0 : τ.H.hom (d.left s) = IsLocalRing.closedPoint τ.V := by
      rw [← Scheme.Hom.comp_apply, Over.w d, hs s]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (spMap τ.j) hr).trans (IsLocalRing.comap_closedPoint τ.j))
    rw [hρ]
    exact (Scheme.Hom.comp_apply _ _ _).symm ▸ (hB p y τ E _ h0).2 (hd trivial)
  refine ⟨N, Over.homMk b₁ hb₁, Over.homMk c₁ hc₁, kb p, inferInstance, t, ρ c₀, ρ b, ρ c, ?_,
    (hρ b).trans hb₂.symm, (hρ c).trans hc₂.symm, ?_⟩
  · rw [hρ, hc₀]
    ext v
    exact ⟨fun ⟨s, h⟩ => h ▸ hx s, fun h => ⟨s₀, (hx _).trans h.symm⟩⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← map_mul] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [key _ h1, key _ h2, key _ h3, key _ h4, key _ h5, key _ h6]

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ModPrim

theorem exists_unit_and_residue_point : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  intro L₁ L₂ p _ V _ j G _ g N N' X _ q H J _ σ cls m hB c w hc hw
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback m.r m.Φ.G.hom G.hom (rPt p ≫ spMap j) := m.cart.1
  have hsq : (rPt p ≫ c) ≫ G.hom = 𝟙 _ ≫ rPt p ≫ spMap j := by
    rw [Category.assoc, hc, Category.id_comp]
  let x : m.Φ.Pt := Over.homMk (pb.lift (rPt p ≫ c) (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ m.r = rPt p ≫ c := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (m.Φ.H_isLB 1) m.F x.left
  have h₁ := m.red x v hv
  rw [hx] at h₁
  have h₂ := CrdCalc.crd_map (IsLocalRing.residue (OO p)) hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h₁ h₂
  have h₃ : Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
    have := CrdCalc.crd_smul u hv
    rwa [← funext hu] at this
  refine ⟨?_, x, hx, h₃⟩
  have hcov := (_root_.GlobalTheory.ZH.ClosedImm.immBy_weight_zero L₁ L₂ (kb p) m.Φ g N N' _ J _ m.F m.pol hB m.good m.dim).1
  have hmem : (x.left : Sp (kb p) ⟶ m.Φ.G.left) (IsLocalRing.closedPoint (kb p)) ∈
      ⨆ i ∈ {i | m.xe.symm (cls i) = 0}, Out.nonzeroLocus (m.F i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi, hm⟩ := hmem
  refine ⟨i, m.xe.symm.map_eq_zero_iff.1 hi, ?_⟩
  have h₄ := (CrdCalc.crd_isUnit_iff i h₃).2 ((CrdCalc.top_le_iff _ _).2 hm)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h₄.ne_zero

end GlobalTheory.ZH.ModPrim
end

