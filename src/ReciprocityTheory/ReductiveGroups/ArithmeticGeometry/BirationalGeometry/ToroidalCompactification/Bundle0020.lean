module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubicalLawRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoVal
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] {L : RigLB A}
  {L' : RigLB A'} (c : CubicalStr A L) (c' : CubicalStr A' L') {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A') (gp : IsGrpPullback A' A f Φ) (w : LB.Iso L'.L (L.L.pull Φ)) (hwg : w.IsGen)
include hG hA hwg

theorem cub_w₀ {T' : Over S'} {z : T'.left} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (x x' y : T' ⟶ A') :
    val (L := L.L) (φ := thφ A (x3 A)) (ε := thε) c.t ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ (cubeMapOf gp).F))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * cubV c' z J' x x' y := by
  have hPG : PGen w := (isGen_iff w).1 hwg
  obtain ⟨t, ht, htv⟩ := exists_up hPG L.isLB L'.isLB (φ' := thφ A' (x3 A')) (ε := thε) c'.t c'.isGen
  have hpt : ∀ I : thK.{0}, thφ A' (x3 A') I ≫ Φ = (cubeMapOf gp).F3 ≫ thφ A (x3 A) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have hFF : FormEq (fun I => thφ A' (x3 A') I ≫ Φ) thε
      (fun I => (cubeMapOf gp).F3 ≫ thφ A (x3 A) I) thε := by
    unfold FormEq
    intro U _ h
    simp only [hpt]
  have hu := pullGen_isGen L.L (thφ A (x3 A)) thε c.t c.isGen (cubeMapOf gp).F3
  have he : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (snd A' (A' ⊗ A')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, lift_fst_snd, Over.id_left]
  have hp := surj_snd hG hA (A' ⊗ A')
  have hE : (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left ≫ (cubeMapOf gp).F3 =
      (lift (1 : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A)
        (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf, pushPt] <;>
      exact congrArg (fun q => q.left) (map_one (pushHom gp (A' ⊗ A')))
  have hvt : ∀ (Z0 : Scheme.{0}) (r : Z0 ⟶ (G3 A').left) (z0 : Z0) (J0 : (Z0 ⟶ A.left) → L.L.ι)
      (J0' : (Z0 ⟶ A'.left) → L'.L.ι), Good L.L z0 J0 → Good L'.L z0 J0' →
      val t r z0 J0 = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z0 (J0 ((r ≫ thφ A' (x3 A') I) ≫ Φ))
        (J0' (r ≫ thφ A' (x3 A') I)) ^ thε I) *
        val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t r z0 J0' := by
    intro Z0 r z0 J0 J0' hJ0 hJ0'
    have hm1 : r z0 ∈ LB.wchart L.L (fun I => thφ A' (x3 A') I ≫ Φ)
        (fun I => J0 (r ≫ (thφ A' (x3 A') I ≫ Φ))) :=
      Set.mem_iInter.2 fun I => hJ0 (r ≫ (thφ A' (x3 A') I ≫ Φ))
    have hm2 : r z0 ∈ LB.wchart L'.L (thφ A' (x3 A')) (fun I => J0' (r ≫ thφ A' (x3 A') I)) :=
      Set.mem_iInter.2 fun I => hJ0' (r ≫ thφ A' (x3 A') I)
    refine (htv Z0 r z0 _ _ hm1 hm2).trans ?_
    simp only [pw, val, Category.assoc] <;> rfl
  have hcov : ∀ q : A'.left, ∃ i, q ∈ L'.L.U i := fun q => by
    have hq : q ∈ (⨆ i, L'.L.U i) := by
      rw [L'.isLB.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hq
  have ac : ∀ {U : Type} [CommGroup U] (a b c d : U), a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = 1 := by
    intro U _ a b c d
    have e1 : a * b⁻¹ * c⁻¹ * a⁻¹ * d * b * c * d⁻¹ = (a * a⁻¹) * (b⁻¹ * b) * (c⁻¹ * c) * (d * d⁻¹) := by
      ac_rfl
    rw [e1]
    simp
  have key := gen_unique' L.isLB hFF (snd A' (A' ⊗ A')).left
    (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left he hp hu ht
    (fun q Jq hJq => by
      obtain ⟨J'q, hJ'q⟩ : ∃ J'q : ((A' ⊗ A').left ⟶ A'.left) → L'.L.ι, Good L'.L q J'q :=
        ⟨fun ψ => Classical.choose (hcov (ψ q)), fun ψ => Classical.choose_spec (hcov (ψ q))⟩
      obtain ⟨hh, hhd⟩ : ∃ hh : ((A' ⊗ A').left ⟶ A'.left) → ((A' ⊗ A').left.presheaf.stalk q)ˣ,
          ∀ ψ, hh ψ = gw w ψ q (Jq (ψ ≫ Φ)) (J'q ψ) := ⟨_, fun _ => rfl⟩
      have f1 : cubV c (T := Over.mk ((A' ⊗ A').hom ≫ f)) q Jq 1
          (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')) = 1 := by
        have e := val_corr hJq (c.face 0) (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))) hJq (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f2 : val (L := L'.L) (φ := thφ A' (x3 A')) (ε := thε) c'.t
          (lift (1 : A' ⊗ A' ⟶ A') (lift (fst A' A') (snd A' A'))).left q J'q = 1 := by
        have e := val_corr hJ'q (c'.face 0) (lift (fst A' A') (snd A' A')).left
        rw [val_one] at e
        refine (Eq.trans ?_ (val_cub c' (lift (fst A' A') (snd A' A')) hJ'q (pzero A' _) (x2 A' 0) (x2 A' 1)).symm).trans e
        congr 1 <;> simp [x2, pzero, Hom.one_def]
      have f3 := prod_cub (T := A' ⊗ A') (1 : A' ⊗ A' ⟶ A') (fst A' A') (snd A' A') hh
      erw [val_pull]
      rw [hE]
      refine f1.trans ?_
      refine Eq.trans ?_ (hvt _ _ q Jq J'q hJq hJ'q).symm
      rw [f2, _root_.mul_one]
      simp only [← hhd]
      rw [f3]
      simp only [_root_.one_mul]
      exact (ac _ _ _ _).symm
      all_goals exact hJq)
    T'.left (lift x (lift x' y)).left z J hJ
  erw [val_pull] at key
  refine key.trans ((hvt _ _ z J J' hJ hJ').trans ?_)
  rfl
  all_goals exact hJ


omit hG hA hwg [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A'] in
def Om {M : LB A.left} {M' : LB A'.left} (w : LB.Iso M' (M.pull Φ)) {Z : Scheme.{0}} {s' : Z ⟶ S'} (z : Z)
    (J : (Z ⟶ A.left) → M.ι) (J' : (Z ⟶ A'.left) → M'.ι) (x : Over.mk s' ⟶ A') : (Z.presheaf.stalk z)ˣ :=
  gw w (show Z ⟶ _ from x.left) z (J (x.left ≫ Φ)) (J' x.left)


omit hG hA hwg in
def cubZ {Z : Scheme.{0}} {s : Z ⟶ S} (z : Z) (J : (Z ⟶ A.left) → L.L.ι) (a b d : Over.mk s ⟶ A) : (Z.presheaf.stalk z)ˣ :=
  cubV c (T := Over.mk s) z J a b d


include gp in
theorem cub_w {Z : Scheme.{0}} {s' : Z ⟶ S'} {s : Z ⟶ S} {z : Z} {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J')
    (a b d : Over.mk s' ⟶ A') (a₀ b₀ d₀ : Over.mk s ⟶ A) (ha : a.left ≫ Φ = a₀.left) (hb : b.left ≫ Φ = b₀.left)
    (hd : d.left ≫ Φ = d₀.left) : cubZ c z J a₀ b₀ d₀ =
      Om w z J J' (a * b * d) * (Om w z J J' (a * b))⁻¹ * (Om w z J J' (a * d))⁻¹ * (Om w z J J' (b * d))⁻¹ * Om w z J J' a *
        Om w z J J' b * Om w z J J' d * (Om w z J J' (1 : Over.mk s' ⟶ A'))⁻¹ * cubZ c' z J' a b d := by
  have hF3 : (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 = (lift a₀ (lift b₀ d₀)).left := by
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, cubeMapOf]
    · exact ha
    · exact hb
    · exact hd
  have h0 := cub_w₀ (c := c) (c' := c') (hG := hG) (hA := hA) (gp := gp) (w := w) (hwg := hwg)
    (hJ := hJ) (hJ' := hJ') (x := a) (x' := b) (y := d)
  rw [hF3] at h0
  refine h0.trans ?_
  congr 1
  exact prod_cub a b d (fun ψ => gw w ψ z (J (ψ ≫ (cubeMapOf gp).F)) (J' ψ))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem twist_of_val {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ} {M : LB A.left}
    (hM : M.IsLB) {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A M b T)} {s' : LB.Sec (LPow A M a T)} (h : ∀ z J, Good M z J →
      sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z J =
      (val α (𝟙 _) z J).val * sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z J) :
    IsTwistPull A M ψ m hm a b α s s' := fun j => fn_ext fun z hz => by
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hM (χ z)
  have hz' : (𝟙 (T ⊗ A).left : _ ⟶ _) z ∈ LB.wchart M ![(snd T A).left, m.left] j := hz
  have a₁ := (gs_res (𝟙 _) z (chart_le_zero A M m j) hz' (s'.f fun _ => j 0)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z (chart_le_zero A M m j hz')
      (Good.mem hJ _ _))
  have a₂ := ((gs_res (𝟙 _) z (chart_le_pull A M ψ m hm j) hz' ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    (gs_pull (𝟙 _) ψ.left z (LB.wchart M (fun _ : Fin 1 => (snd T A).left) fun _ => j 1) (chart_le_pull A M ψ m hm j hz') _)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z
      (chart_le_pull A M ψ m hm j hz') (Good.mem hJ _ _))
  have a₃ := (gs_unit (𝟙 _) z _ hz' (α.s j)).trans (congrArg Units.val (gen_trans hα (𝟙 _) z hz' (Good.mem hJ _ _)))
  refine a₁.trans (Eq.trans ?_ ((gs_mul (𝟙 _) z _ hz' _ _).trans (congrArg₂ (· * ·) a₃ a₂)).symm)
  refine (congrArg (_ * ·) (h z J hJ)).trans ?_
  have e : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, ← Over.comp_left, hm]
  have t : trF (L := M) (K := Fin 2) ![(snd T A).left, m.left] ![a, -b] (𝟙 _) z j
        (fun k => J (𝟙 _ ≫ (![(snd T A).left, m.left] : Fin 2 → _) k)) *
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => b) (𝟙 _ ≫ ψ.left) z (fun _ => j 1)
        (fun _ => J ((𝟙 _ ≫ ψ.left) ≫ (snd T A).left)) =
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _) z (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) := by
    rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
    exact (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) ((congrArg (· * _) (zpow_neg _ _)).trans (inv_mul_cancel _))).trans
      (_root_.mul_one _))
  rw [← t, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  rfl

variable [IsCommMonObj A] {L : RigLB A}

theorem isMonHom_mulA (n : ℕ) : IsMonHom (mulA A n) := by
  constructor
  · rw [mulA, MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  · have e := MonObj.mul_eq_mul A
    rw [mulA, MonObj.comp_pow, Category.comp_id]
    conv_lhs => rw [e, mul_pow]
    rw [e, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id]

omit [IsCommMonObj A] [GrpObj A] in
theorem prod_end (φ : A ⟶ A) {a b : ℕ} {a' b' : ℤ} (ha : a' = a) (hb : b' = b) {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U]
    (h : (T.left ⟶ A.left) → U) : ∏ i, h (y.left ≫ (![𝟙 A.left, φ.left] : Fin 2 → _) i) ^ (![a', -b'] : Fin 2 → ℤ) i =
      h y.left ^ a * (h (y ≫ φ).left ^ b)⁻¹ := by
  subst ha hb
  rw [Fin.prod_univ_two]
  simp [Over.comp_left, zpow_neg, zpow_natCast]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

