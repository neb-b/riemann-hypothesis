module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.InducingAut

open GlobalTheory.FieldBaseChange

theorem exists_const_ratio {K : Type} [CommRing K] {Y : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (p : Y ⟶ Spec (CommRingCat.of K)) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ N.U i →
      (gm r z (N.U i) (t₁.s i)).val = constVal (r ≫ p) z c * (gm r z (N.U i) (t₂.s i)).val := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp u.val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z i hi => ?_⟩
  have key : (gm r z (N.U i) (t₁.s i) * (gm r z (N.U i) (t₂.s i))⁻¹).val = constVal (r ≫ p) z c := by
    rw [← map_inv, ← map_mul, ← hu i, gm_res r z _ hi]
    exact (gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial _))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem constVal_pow {K : Type} [CommRing K] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of K)) (z : Z) (c : K)
    (k : ℕ) : constVal π z (c ^ k) = constVal π z c ^ k := by
  simp only [constVal, gs_eq π z ⊤ trivial, map_pow]

theorem isoRelM_change {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w w' : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {g₂ : Z₂ ⟶ X₂} {h₂ : Y' ⟶ Z₂}
    {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)} (c : S)
    (hc : ∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
      (isoVal w' (𝟙 Y' ≫ m) y i₂ i₁).val =
        constVal ((𝟙 Y' ≫ h₁) ≫ π₁) y c * (isoVal w (𝟙 Y' ≫ m) y i₂ i₁).val)
    {a : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w' m k g₁ h₁ a g₂ h₂ b) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c ^ k • a : SecOver π₁ _) g₂ h₂ b := by
  refine (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).2 fun y i₂ i₁ a₂ a₁ => ?_
  have b₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ :=
    (congrArg (fun q : Y' ⟶ X₁ => q y) h.1 : g₁ (h₁ y) = f₁ (m y)).symm ▸ a₁
  rw [powVal_smul _ _ _ y b₁, (isoRelM_iff w' m k h₁ h.1 _ h.2.1 _ _).1 h _ (𝟙 _) y i₂ i₁ a₂ a₁,
    zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hc y i₂ i₁ a₂ a₁,
    constVal_pow]
  ring

theorem mul_chart_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (g : Y ⟶ X) {a b c : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => a)))
    (s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => b)))
    (s'' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => c))) :
    (∀ j, @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s''.f j) =
      @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s'.f j)) ↔
    ∀ y J, Good L y J → sval s'' (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J := by
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (gs_mul _ y _ (hJ.mem (fun _ : Fin 1 => g) (𝟙 Y)) _ _)
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Fin 1 => 𝟙 Y ≫ g) j
      (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
    have := h y J hJ
    rw [sval_of s _ y J j e, sval_of s' _ y J j e, sval_of s'' _ y J j e] at this
    exact this.trans (gs_mul _ y _ hy _ _).symm

section Frames

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_frame (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : ∃ w : Frm D F k b, w.IsGen :=
  exists_gen_of_local (V := F) D.P.L D.P.isLB _ _


variable {D F} in
theorem exists_frame_pow {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen) (n : ℕ) :
    ∃ ω : Frm D F (k * n) b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨ω, h, v⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k * n))
    (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg _ (by
      fin_cases i <;> simp [DegPre.lineε, mul_comm]))
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ w hw n)
  exact ⟨ω, h, fun z J hJ => (v _ _ z J hJ).trans (map_pow _ _ _)⟩

end Frames

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expandsF_change (hG : GlobalFnsSt) (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, ∀ (t : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k),
      U.ExpandsF F k w' t s → U.ExpandsF F k w (c • t : SecOver (abelianBase A F) _) s := by
  have : IsIso U.gen.hom.left := ⟨⟨U.gen.inv.left, by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]⟩⟩
  have hp : Function.Surjective (U.gen.hom.left ≫ A.A.hom).appTop.hom := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso U.gen.hom.left.appTop).2.comp (hG _ _ A.isAb).2
  obtain ⟨c, hc⟩ := exists_const_ratio (K := FractionRing R) (fun y => by
    obtain ⟨i, hi⟩ := exists_chart A.isLB (U.gen.hom.left y)
    obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (pullback.fst G.hom (jK R) y)
    exact ⟨(fun _ => j, fun _ => i), mem_pull.2 hj, mem_pull.2 hi⟩) (U.gen.hom.left ≫ A.A.hom) hp hw' hw
  refine ⟨algebraMap (FractionRing R) F c ^ k, ?_⟩
  rintro t s ⟨v, a, b⟩
  refine ⟨v, isoRelM_change (π₁ := abelianBase A F) _ (fun y i₂ i₁ a₂ a₁ => ?_) a, b⟩
  refine (hc _ _ y (fun _ => i₂, fun _ => i₁) ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩).trans (congrArg (· * _) ?_)
  refine Eq.trans (congrArg (fun q => constVal q y c) ?_) (constVal_specMap _ (algebraMap (FractionRing R) F) y c)
  have hπ : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
    congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  simp only [Category.id_comp]
  rw [hπ, e]
  exact (isPullback_groupBase F).w

theorem exists_transport (hG : GlobalFnsSt) (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {N : ℕ} (hN : 1 ≤ N) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) (Φ : Fam D.toPre F N →ₗ[F] Fam D.toPre F N)
    (hΦ : Function.Bijective Φ) :
    ∃ Ψ : SecA A F N ≃ SecA A F N,
      (∀ (s s' s'' : SecA A F N) (c : Γ((TFK (R := R) F).left, ⊤)),
        (∀ j, s''.f j = liftFun A.A _ c * s.f j + s'.f j) →
          ∀ j, (Ψ s'').f j = liftFun A.A _ c * (Ψ s).f j + (Ψ s').f j) ∧
      (∀ t, ∃ s, U.ExpandsF F N w₀ t s ∧ U.ExpandsF F N w₀ (Ψ t) (Φ s)) ∧
      ∀ w₁ : W0 U.toUnifPre, w₁.IsGen → ∀ t s s', U.ExpandsF F N w₁ t s → U.ExpandsF F N w₁ (Ψ t) s' →
        s' = Φ s := by
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
  let Ψ := (e.trans (LinearEquiv.ofBijective Φ hΦ)).trans e.symm
  have hΨ : ∀ t, e (Ψ t) = Φ (e t) := fun t => e.apply_symm_apply _
  refine ⟨Ψ.toEquiv, fun s s' s'' c h j => ?_, fun t => ⟨e t, (he _ _).2 rfl, (he _ _).2 (hΨ t)⟩,
    fun w₁ hw₁ t s s' h h' => ?_⟩
  · obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c
    let t : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s
    let t' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s'
    let t'' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s''
    have e₁ : t'' = c • t + t' := SecOver.ext _ _ fun j => (h j).trans rfl
    have e₂ : Ψ t'' = c • Ψ t + Ψ t' := by rw [e₁, map_add (f := _), map_smul]
    exact (congrArg (chartFun _ _ j) e₂).trans rfl
  · obtain ⟨c, hc⟩ := expandsF_change hG U.toUnifPre F N hw₀ hw₁
    have a := (he _ _).1 (hc t s h)
    have a' := (he _ _).1 (hc (Ψ t) s' h')
    exact a'.symm.trans ((e.map_smul c _).trans ((congrArg (c • ·) (hΨ t)).trans
      ((Φ.map_smul c _).symm.trans (congrArg Φ ((e.map_smul c t).symm.trans a)))))

end Unif


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_qk_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k) (n : ℕ) :
    ∃ h : GtPtF D F, GtPtF.IsNsmul (k * n) p.g h ∧ GtPtF.IsIota (n • p.y) h :=
  (GlobalTheory.TorusExt.qkMk hB (k := k * n) (n • p.y) p.g (by
    rw [map_nsmul, ← GlobalTheory.TorusExt.qk_nsmul hB p, mul_nsmul])).eq

theorem exists_aut : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  intro hL R _ _ _ I hI D A G _ _ hS U F _ _ _ k hk p
  have hG := hL.1.globalFns
  have hN : ∀ n, 1 ≤ k * (n + 1) := fun n => Nat.mul_pos hk n.succ_pos
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨w, hw⟩ := exists_frame D.toPre F k p.g.b
  choose ω hω vω using fun n => exists_frame_pow w hw (n + 1)
  let q : ∀ n, QkPt D.toPre F (k * (n + 1)) := fun n =>
    ⟨(n + 1) • p.y, p.g, exists_qk_mul D.tau_bimult p (n + 1)⟩
  choose Φ hΦ using fun n => _root_.GlobalTheory.UT.PhiProj.phi_projective hL R I hI D F (k * (n + 1)) (hN n)
  have hΦ' := fun n => (hΦ n).1 (q n) (ω n) (hω n)
  choose Ψ lin ex un using fun n => exists_transport hG U F (hN n) hw₀ _ (hΦ' n).1
  have mul : ∀ m : Fin 3 → ℕ, m 2 = m 0 + m 1 + 1 → ∀ t : ∀ i, SecA A F (k * (m i + 1)),
      (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) →
      ∀ z J, Good A.L z J → sA (Ψ _ (t 2)) (𝟙 _) z J = sA (Ψ _ (t 0)) (𝟙 _) z J * sA (Ψ _ (t 1)) (𝟙 _) z J := by
    intro m hm t
    choose s hs hs' using fun i => ex (m i) (t i)
    exact _root_.GlobalTheory.UT.PhiMul.phi_mul hL R I hI D A G hS U F w₀ hw₀ k hk p w hw (fun i => m i + 1) (fun i => k * (m i + 1))
      (fun i => ⟨Nat.succ_pos _, rfl⟩) (by show m 2 + 1 = m 0 + 1 + (m 1 + 1); omega) (fun i => q (m i))
      (fun i => ω (m i)) (fun i => ⟨rfl, rfl, hω _, vω _⟩) t (fun i => Ψ _ (t i)) s _
      (fun i => ⟨hs i, hs' i, ((hΦ' _).2 _ _).2 rfl⟩)
  obtain ⟨ψ, hψ, hα⟩ := GlobalTheory.T.exists_automorphism_of_multiplicative_section_family F _ A (jFK (R := R) F) k hk Ψ lin (fun a b s s' s'' h =>
    (mul_chart_iff A.isLB _ _ _ _).2 (mul ![a, b, a + b + 1] rfl
      (Fin.cons s (Fin.cons s' (Fin.cons s'' finZeroElim))) ((mul_chart_iff A.isLB _ _ _ _).1 h)))
  refine ⟨ψ, fun n N hn hN' q' hy hg => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hN'
  obtain rfl : q' = q n := GlobalTheory.TorusExt.qk_ext hy hg
  obtain ⟨α, hα, tw⟩ := hα n
  refine ⟨hψ, fun w₁ hw₁ => ⟨α, ω n, hα, hω n, fun t t' s s' h h' H => ?_⟩⟩
  obtain rfl : t' = Ψ n t := sec_ext' A.isLB fun y J hJ =>
    (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A H (𝟙 _) y hJ).trans
      (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A (tw t) (𝟙 _) y hJ).symm
  exact ((hΦ' n).2 _ _).2 (un n w₁ hw₁ t s s' h h')

end GlobalTheory.InducingAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismAlgebraisingThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndAlg

variable {X X' : Scheme.{0}} {κ : Type}

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A)
    {P : MvPolynomial σ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => x j * c) P = MvPolynomial.eval₂ φ x P * c ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := hP (MvPolynomial.mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, _root_.mul_one, Finsupp.sum] at hd'
  rw [← hd']
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, _root_.mul_assoc]

theorem gs_eval {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (U : X.Opens)
    (h : φ z ∈ U) (x : κ → Γ(X, U)) (P : MvPolynomial κ R) :
    gs φ z U (MvPolynomial.eval₂Hom (cst f U) x P) =
      MvPolynomial.eval₂ ((X'.presheaf.germ ⊤ z trivial).hom.comp (cst (φ ≫ f) ⊤)) (fun j => gs φ z U (x j)) P := by
  rw [gs_eq φ z U h, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply]
    rw [← gs_eq φ z U h]
    simp only [GlobalTheory.AbLaw.cst, rs, RingHom.comp_apply]
    rw [gs_res φ z le_top h, gs_eq φ z ⊤ trivial]
    have hid : X'.presheaf.map (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      exact X'.presheaf.map_id _
    rw [hid]
    simp only [CommRingCat.hom_id, RingHom.id_apply]
    rfl
  · funext j
    simp only [Function.comp_apply]
    exact (gs_eq φ z U h _).symm

theorem isUnit_gs_iff (r : X' ⟶ X) (z : X') (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  refine (X'.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good M z J →
      sval t r z J = gs (r ≫ π) z _ (s.f (J (r ≫ π))) := by
  have hle : ∀ j : PUnit → M.ι, LB.wchart M (fun _ : PUnit => π) j ≤ π ⁻¹ᵁ M.U (j ⟨⟩) :=
    fun _ _ hy => Set.mem_iInter.1 hy ⟨⟩
  refine ⟨⟨fun j => (X'.presheaf.map (homOfLE (hle j)).op).hom ((π.app (M.U (j ⟨⟩))).hom (s.f (j ⟨⟩))),
    fun i j => ?_⟩, ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic π (hle i) (hle j) (s.f _) (s.f _) _ (s.compat _ _) _ ?_
    show (∏ k : PUnit, _) = _
    rw [Fintype.prod_unique, zpow_one]
  · intro Z r z J hJ
    have hm := hJ.mem (fun _ : PUnit => π) r
    have hz : (r ≫ π) z ∈ M.U (J (r ≫ π)) := hJ (r ≫ π)
    show gs r z _ ((X'.presheaf.map (homOfLE (hle _)).op).hom ((π.app _).hom (s.f _))) = _
    rw [gs_res r z (hle _) hm, gs_pull r π z _ hz]

theorem exists_prod {H : LB X} (hH : H.IsLB) (p g : X' ⟶ X) (t : ℤ) (s : LB.Sec H)
    (u : LB.Sec (LB.LinComb H (K := Fin 2) ![p, g] ![t, -1])) :
    ∃ w : LB.Sec (LB.LinComb H (K := PUnit) (fun _ => p) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ g) z _ (s.f (J (r ≫ g))) * sval u r z J := by
  obtain ⟨t0, ht0⟩ := exists_pull s g
  have hF : FormEq (Sum.elim (fun _ : PUnit => g) ![p, g]) (Sum.elim (fun _ : PUnit => (1 : ℤ)) ![t, -1])
      (fun _ : PUnit => p) (fun _ => t) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨w, hw⟩ := exists_sec hH hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec t0 u)
  refine ⟨w, fun Z r z J hJ => ?_⟩
  rw [hw Z r z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec t0 u r z hJ, ht0 Z r z J hJ]

private theorem gs_sec_chart_transition {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (ψ : Z ⟶ X) (z : Z) (k k' : H.ι)
    (hk : ψ z ∈ H.U k) (hk' : ψ z ∈ H.U k') :
    gs ψ z (H.U k) (s.f k) = gs ψ z (H.U k ⊓ H.U k') (H.g k k' : Γ(X, H.U k ⊓ H.U k')) * gs ψ z (H.U k') (s.f k') := by
  have hkk : ψ z ∈ H.U k ⊓ H.U k' := TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩
  rw [← gs_res ψ z (inf_le_left : H.U k ⊓ H.U k' ≤ H.U k) hkk, s.compat k k', gs_mul ψ z _ hkk,
    gs_res ψ z inf_le_right hkk]

theorem exists_end_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, f e ≫ Y.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Y, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI Y hsm hpr f hf hfc
  obtain ⟨H, hH, n, s, hva⟩ := id hpr
  obtain ⟨t, m, u, hcov, hu⟩ := GlobalTheory.T.exists_compatible_generatingSections_all_thickenings R I Y H n s hsm hH hva f hfc
  have hw0 : ∀ e (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ w : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => pullback.fst Y.hom (thick R I e)) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ f e) z _ ((s i).f (J (r ≫ f e))) * sval (u e j) r z J :=
    fun e i j => exists_prod hH (pullback.fst Y.hom (thick R I e)) (f e) t (s i) (u e j)
  choose w hw using hw0
  have hS0 : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ S : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => 𝟙 Y.left) (fun _ => t)),
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval S (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (w e i j) r z J := by
    intro i j
    refine _root_.GlobalTheory.SecAlgLinComb.exists_sec_linComb R I hI Y hsm hpr Y.left H PUnit (fun _ => 𝟙 Y.left) (fun _ => t)
      (fun e _ => pullback.fst Y.hom (thick R I e)) hH (fun e k => Category.comp_id _) (fun e => w e i j) ?_
    intro e z J hJ
    rw [hw (e + 1) i j _ _ z J hJ, hw e i j _ _ z J hJ, hfc e, Category.id_comp, hu e j z J hJ]
  choose S hS using hS0
  have hN : (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).IsLB := LB.isLB_linComb hH _ _
  have key : ∀ e (z : (thickObj R I e Y).left) (k' : PUnit → H.ι),
      pullback.fst Y.hom (thick R I e) z ∈ H.U (k' ⟨⟩) →
      ∃ J, Good H z J ∧ f e z ∈ H.U (J (f e)) ∧ ∀ i j,
        gs (pullback.fst Y.hom (thick R I e)) z
            ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k') ((S i j).f k') =
          gs (f e) z (H.U (J (f e))) ((s i).f (J (f e))) * sval (u e j) (𝟙 _) z J := by
    intro e z k' hz
    obtain ⟨J, hJ, hJk⟩ := exists_good H hH z (fun _ : PUnit => 𝟙 _ ≫ pullback.fst Y.hom (thick R I e))
      (fun _ => k' ⟨⟩) (fun _ _ _ => rfl) (fun _ => by simpa using hz)
    refine ⟨J, hJ, hJ (f e), fun i j => ?_⟩
    have h1 := (hS i j e _ (𝟙 _) z J hJ).trans (hw e i j _ (𝟙 _) z J hJ)
    rw [sval_of (S i j) _ z J k' (fun k => by cases k; simpa using hJk ⟨⟩)] at h1
    rw [Category.id_comp, Category.id_comp] at h1
    exact h1
  have hcov' : (⨆ i, ⨆ j, nonzeroLocus (S i j)) = ⊤ := by
    have hjac : I ≤ (⊥ : Ideal R).jacobson := by have := hI; exact IsAdicComplete.le_jacobson_bot (I := I)
    have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R Y.left Y.hom hpr
    refine _root_.GlobalTheory.Unif.eq_top_of_special_part R I hjac Y _ fun z => ?_
    have hz1 : z ∈ ⨆ j, nonzeroLocus (u 0 j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz1
    unfold nonzeroLocus at hj
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hz2 : f 0 z ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz2
    unfold nonzeroLocus at hi
    obtain ⟨kk0, hkk0⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hkU : z ∈ LB.wchart H ![pullback.fst Y.hom (thick R I 0), f 0] k := Scheme.basicOpen_le _ _ hk
    have hq : pullback.fst Y.hom (thick R I 0) z ∈ H.U (k 0) := Set.mem_iInter.1 hkU 0
    obtain ⟨J, hJ, hJe, hv⟩ := key 0 z (fun _ => k 0) hq
    have hqN : pullback.fst Y.hom (thick R I 0) z ∈
        (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U (fun _ => k 0) :=
      Set.mem_iInter.2 fun _ => hq
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
    unfold nonzeroLocus
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k 0, ?_⟩
    rw [← isUnit_gs_iff _ _ _ hqN, hv i j]
    refine IsUnit.mul ?_ ?_
    · have hm0 : f 0 z ∈ H.U kk0 := Scheme.basicOpen_le _ _ hkk0
      have hu0 := (isUnit_gs_iff (f 0) z (H.U kk0) hm0 ((s i).f kk0)).2 hkk0
      rw [gs_sec_chart_transition (s i) (f 0) z kk0 (J (f 0)) hm0 hJe] at hu0
      exact isUnit_of_mul_isUnit_right hu0
    · have hm := hJ.mem ![pullback.fst Y.hom (thick R I 0), f 0] (𝟙 _)
      rw [sval_of (u 0 j) (𝟙 _) z J _ (fun _ => rfl), sec_trans (u 0 j) (𝟙 _) z hm hkU]
      exact (Units.isUnit _).mul ((isUnit_gs_iff _ _ _ hkU _).2 hk)
  have hrel : ∀ i i' j j' k, (S i j).f k * (S i' j').f k = (S i j').f k * (S i' j).f k := by
    intro i i' j j' k
    have hF : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3 :
        MvPolynomial (Fin 4) R).IsHomogeneous 2 :=
      ((MvPolynomial.isHomogeneous_X R 0).mul (MvPolynomial.isHomogeneous_X R 1)).sub
        ((MvPolynomial.isHomogeneous_X R 2).mul (MvPolynomial.isHomogeneous_X R 3))
    have h := _root_.GlobalTheory.FormVan.form_eq_zero R I hI Y hsm hpr _ (Fin 4) ![S i j, S i' j', S i j', S i' j] 2 _ hN hF ?_ k
    · simpa [sub_eq_zero] using h
    · intro e z k hz
      obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
      rw [gs_eval Y.hom _ z _ hz]
      simp [hv]
      ring
  have hhom : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d →
      (∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom (H.U k)) (fun i => (s i).f k) F = 0) →
      ∀ j k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k))
        (fun i => (S i j).f k) F = 0 := by
    intro d F hF h0 j
    refine _root_.GlobalTheory.FormVan.form_eq_zero R I hI Y hsm hpr _ (Fin (n + 1)) (fun i => S i j) d F hN hF ?_
    intro e z k hz
    obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
    rw [gs_eval Y.hom _ z _ hz]
    simp only [hv]
    have h2 := gs_eval Y.hom (f e) z (H.U (J (f e))) hJe (fun i => (s i).f (J (f e))) F
    rw [h0, hf e] at h2
    have hz0 : gs (f e) z (H.U (J (f e))) 0 = 0 := by rw [gs_eq _ _ _ hJe, map_zero, map_zero]
    rw [eval₂_scale _ (sval (u e j) (𝟙 _) z J) (fun i => gs (f e) z (H.U (J (f e))) ((s i).f (J (f e)))) hF,
      ← h2, hz0, zero_mul]
  obtain ⟨φ, hφ, huniq⟩ := _root_.GlobalTheory.RankMap.exists_hom_of_rank_one R Y.left Y.hom H n s hH hva Y.left Y.hom _ m S hN hcov' hrel hhom
  refine ⟨Over.homMk φ hφ, fun e => ?_⟩
  refine huniq _ (pullback.fst Y.hom (thick R I e)) (f e) (hf e) ?_
  intro z k k' i i' j hzk hzk'
  obtain ⟨J, hJ, hJe, hv⟩ := key e z k' (Set.mem_iInter.1 hzk' ⟨⟩)
  rw [hv, hv, gs_sec_chart_transition (s i) (f e) z k (J (f e)) hzk hJe, gs_sec_chart_transition (s i') (f e) z k (J (f e)) hzk hJe]
  ring

end GlobalTheory.EndAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeOfCompatibleThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAbelianScheme_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsCommMonObj (Y e)) → IsProjBy B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e) := by
  intro V _ _ _ _ Y _ β hβ B b hA hc hP hb hβb
  have hprop : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hP
  have hsm : Smooth B.hom := by
    refine GlobalTheory.SmoothLimit.main V B fun e ↦ ?_
    have h : Smooth (Y e).hom := (hA e).smooth
    have he : (thickObj V (IsLocalRing.maximalIdeal V) e B).hom =
        (hb e).isoPullback.inv ≫ (Y e).hom := ((hb e).isoPullback_inv_snd).symm
    have h' : Smooth ((hb e).isoPullback.inv ≫ (Y e).hom) := inferInstance
    exact he ▸ h'
  have hconn : GeometricallyConnected B.hom :=
    GlobalTheory.ConnFibre.geometricallyConnected_of_closedFibre V B hsm hP (Y 0) (b 0) (hb 0)
      (hA 0).geomConnected
  obtain ⟨mu, io, un, H⟩ := _root_.GlobalTheory.GrpAlg.exists_group_operations V Y β hβ B b hP inferInstance hb hβb
  obtain ⟨G, hG, hcomm⟩ := GlobalTheory.grpObj_of_thickenings V Y β hβ B b hb hβb mu io un H
  exact ⟨G, hcomm hc, ⟨hcomm hc, hsm, hprop, hconn⟩, hG⟩

end GlobalTheory
end

