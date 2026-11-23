module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiWZeroPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem rel_on (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty) {K : Type} [Fintype K]
    {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.xK a)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi a) D.rigK)) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (LB.pullGen D.P.L _ _ u (cP D (TW W) a).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi a) (D.rigW W)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ h (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vψ, vρ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    refine congrArg (fun q => val u q z J) ?_
    rw [Category.id_comp]
    exact congrArg (fun q => q.left) (comp_cP D κ a)

end OnW

theorem prod_four {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (f : A ⟶ A) (x : T ⟶ A) {U : Type}
    [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) i) ^
      (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      k (x * (x ≫ f)).left * (k x.left ^ 2)⁻¹ * (k (x ≫ f).left)⁻¹ * k (1 : T ⟶ A).left ^ 2 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ (𝟙 A * f)).left ^ (1 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) * k (x ≫ f).left ^ (-1 : ℤ) *
    k (x ≫ 1).left ^ (2 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg_one, zpow_neg, zpow_ofNat, zpow_ofNat]

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

set_option maxHeartbeats 1000000 in
theorem traceFormTwistIso_of_pullback (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by
  obtain ⟨u, hu, hn, hrel⟩ := h
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have ha : (ιD'.onB.act w0).left ≫ Φ = Φ ≫ (ιD.onB.act w0).left := by
    have a₂ : ((Over.pullback (specOf φ)).map (ιD.onB.act w0)).left ≫ pullback.fst D.P.A.hom (specOf φ) =
        pullback.fst _ _ ≫ (ιD.onB.act w0).left := pullback.lift_fst _ _ _
    show _ ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, a₂, Category.assoc]
  have hψ : ∀ k : Fin 4, (![(padd D'.P.A (𝟙 _) (ιD'.onB.act w0)).left, 𝟙 D'.P.A.left, (ιD'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → _) k ≫ Φ =
      Φ ≫ (![(padd D.P.A (𝟙 _) (ιD.onB.act w0)).left, 𝟙 D.P.A.left, (ιD.onB.act w0).left,
      (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k := by
    have p1 : (pushPt gp.1.w (𝟙 D'.P.A)).left = Φ := Category.id_comp _
    intro k
    fin_cases k
    · have m : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) * pushPt gp.1.w (ιD'.onB.act w0) := map_mul (pushHom gp D'.P.A) _ _
      have q : pushPt gp.1.w (ιD'.onB.act w0) = pushPt gp.1.w (𝟙 D'.P.A) ≫ ιD.onB.act w0 :=
        Over.OverMorphism.ext (by rw [Over.comp_left, p1]; exact ha)
      have m' : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) ≫ (𝟙 D.P.A * ιD.onB.act w0) := by
        rw [m, q, MonObj.comp_mul, Category.comp_id]
      have := congrArg (fun q => q.left) m'
      simp only [Over.comp_left, p1] at this
      exact this
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact ha
    · have m : pushPt gp.1.w (1 : D'.P.A ⟶ D'.P.A) = pushPt gp.1.w (𝟙 D'.P.A) ≫ (1 : D.P.A ⟶ D.P.A) := by
        rw [MonObj.comp_one]; exact map_one (pushHom gp D'.P.A)
      have := congrArg (fun q => q.left) m
      simp only [Over.comp_left, p1] at this
      exact this
  obtain ⟨u', hu', pmu⟩ := exists_pmaps ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB Φ hψ u hu
  have vu : ∀ {T : Over (Spec (CommRingCat.of R'))} (x : T ⟶ D'.P.A) (z : T.left) J J', Good D.P.L z J →
      Good D'.P.L z J' → ∀ Ω : (T ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, Ω x = gw hD.w x.left z (J (x.left ≫ Φ)) (J' x.left)) → val u (x.left ≫ Φ) z J =
        Ω (x * (x ≫ ιD'.onB.act w0)) * (Ω x ^ 2)⁻¹ * (Ω (x ≫ ιD'.onB.act w0))⁻¹ * Ω 1 ^ 2 * val u' x.left z J' :=
    fun x z J J' hJ hJ' Ω hΩ => by
      rw [hΩ, hΩ, hΩ, hΩ]
      exact (pmaps_val hψ pmu x.left z hJ hJ').trans (congrArg₂ (· * ·)
        (prod_four (ιD'.onB.act w0) x (fun q => gw hD.w q z (J (q ≫ Φ)) (J' q))) rfl)
  refine ⟨u', hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun a => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have := ιD'.onB.hom w0
    have e := vu (1 : 𝟙_ _ ⟶ D'.P.A) y J J' hJ hJ' _ (fun _ => rfl)
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have b := val_corr hJ hn (specOf φ)
    rw [val_pull hJ, val_one, ← hD.he] at b
    rw [MonObj.one_comp, _root_.mul_one, e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    have e' := congrArg Additive.ofMul (b.symm.trans e)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ :=
      fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
    have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
      fun χ => val_psiW hD hJ hJ' χ
    have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
      have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
        (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
      have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
        congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
      have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
        (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
      rw [Fintype.prod_unique, zpow_one] at e
      have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
      have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
      rw [b₁, b₂]
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
    have cW : hD.g ≫ (cP D (TW hD.W) (hD.xe a)).left = (cP D' (TK R') a).left ≫ Φ := by
      have hx : (cP D' (TK R') a).left ≫ Φ = jK R' ≫ specOf φ ≫ (D.c (hD.xe a)).left := by
        rw [← hD.c_pr a, ← Category.assoc]; rfl
      rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
    have cl : cP D' (TK R') a ≫ ιD'.onB.act w0 = cP D' (TK R') (w0 • a) := by
      rw [cP, cP, ιD'.c_lin, Category.assoc]
    have key := (val_mul hJ _ _ _).symm.trans ((val_corr hJ
      (rel_on hD.psiW ⟨_, (hD.g y).2⟩ u _ _ (hrel (hD.xe a))) hD.g).trans (val_mul hJ _ _ _))
    rw [val_pull hJ, cW, vu (cP D' (TK R') a) y J J' hJ hJ' Ω (fun _ => rfl), cl, val_tauW _ _ hJ, ← hx, ← map_add (f := _),
      vψ, vψ, vψ, vρ, cPoint_add] at key
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    have b : val (LB.pullGen D'.P.L _ _ u' (D'.xK a)) (𝟙 _) y J' = val u' (cP D' (TK R') a).left y J' := by
      rw [val_pull hJ', Category.id_comp]; rfl
    rw [b, val_tau _ hJ']
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul key
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'

end Pull

end PsiWZeroPull

theorem traceFormTwistIso_of_overPullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X]
    [Module O D'.X] (ιD : D.OAct O) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) →
    (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) →
    ∀ w0 : O, Geo.Tor.TraceFormTwistIso D ιD w0 → Geo.Tor.TraceFormTwistIso D' ιD' w0 :=
  fun _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ ιD ιD' hx hact w0 h => PsiWZeroPull.traceFormTwistIso_of_pullback hD ιD ιD' hx hact w0 h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.QkPairing

theorem cub_comm {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ) (a m b x : A)
    (Sa Sy Say τa τy τay ζ : U) (h₁ : Say * θ a (m ^ k) b = Sa * Sy) (h₂ : τay * θ a (b ^ k) m = τa * τy)
    (h₃ : τy * cubN θ k 1 b m = ζ * (Sy * cubN θ k 1 m b)) :
    cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) =
      ζ * (cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Say)) := by
  have e₀ := h.N_split k a m b
  have e₁ := h.N_add k a m x b
  have e₂ := h.N_add k a b x m
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k (a * b ^ k) m x
  have e₅ := h.N_split k a m x
  have e₆ := h.N_split k a b x
  have e₇ := h.N_split k a b m
  have e₈ := h.coc a (m ^ k) (b ^ k) x
  have e₉ := h.coc a (b ^ k) (m ^ k) x
  rw [mul_comm (b ^ k), h.s01 (b ^ k)] at e₉
  have f₁ := h.coc x b m a
  have f₂ := h.coc x m b a
  rw [mul_comm m b, h.s01 m b a] at f₂
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b] at f₁
  rw [h.s12 (x * m), h.s01 (x * m), h.s12 x m a, h.s01 x a m] at f₂
  have f₃ : θ b x m = θ m x b := by rw [h.s01 b, h.s12 x, h.s01 x]
  rw [f₃] at e₂
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈; have a₉ := E e₉; have b₁ := E f₁; have b₂ := E f₂
  have c₁ := E h₁; have c₂ := E h₂; have c₃ := E h₃
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) -(a₁ - a₂ + a₃ - a₄ + a₅ - a₆ - a₇ + a₈ - a₉ - b₁ + b₂ + c₁ - c₂ - c₃ + a₀)

theorem exists_const {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {F : Type} [Field F] {K : Type} [Fintype K]
    {φ : K → (Spec (CommRingCat.of F) ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb M φ ε)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of F) ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ ζ : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (Spec (CommRingCat.of F) ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (res le (t.s PEmpty.elim)),
    fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    (congrArg (gs r z ⊤) ?_))
  exact ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _).symm

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

def IsRatio (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
    (val (p.g.s p'.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p'.g.b) (σ ≫ p.g.b)).val =
      gs σ.left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) *
        (val (p'.g.s p.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p.g.b) (σ ≫ p'.g.b)).val

theorem exists_ratio (p p' : QkPt D F k) : ∃ ζ : Fˣ, IsRatio p p' ζ.val := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub 1 p'.g.b p.g.b k
  obtain ⟨N', hN', vN'⟩ := exists_cubN D.cub 1 p.g.b p'.g.b k
  obtain ⟨ζ, hζ⟩ := exists_const D.P.isLB (F := F)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (p.g.s p'.y) N)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (p'.g.s p.y) N')))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen _) hN)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p'.g.isGen _) hN'))) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 8) (K' := Fin 4 ⊕ Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p.g.b p'.y h) rfl)
        (prod_neg _ _ (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p'.g.b p.y h) rfl))).trans ?_
      rw [cPoint_y, cPoint_y]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, mul_comm p.g.b p'.g.b]
      module)
  refine ⟨ζ, fun T σ z J hJ => ?_⟩
  have e := hζ _ σ.left z J hJ
  rw [val_mul hJ, val_inv, val_mul hJ, val_mul hJ, vN T σ z J hJ, vN' T σ z J hJ, MonObj.comp_one] at e
  rw [← e, ← Units.val_mul, inv_mul_cancel_right]

theorem weil_of_ratio (hG : GlobalFnsSt) (p p' : QkPt D F k) {ζ : Fˣ} (H : IsRatio p p' ζ.val) :
    WeilQkIs D F k p p' ζ.val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
  rw [phiRel_iff hG _ _ hw'] at r₁ r₄
  rw [phiRel_iff hG _ _ hw] at r₂ r₃
  rw [isSmul_iff]
  refine fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y + p.y = β := ⟨β - p.y - p'.y, by abel⟩
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hy : ∀ q : QkPt D F k, cP D (DegPre.BF D F) q.y = (fst (TF (R := R) F) D.P.A ≫ q.g.b) ^ k := fun q => by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _
  have e₂ := r₂ (α + p'.y) _ rfl _ (𝟙 _) y J hJ
  have e₁ := r₁ α _ rfl _ (DegPre.trPt D F p.g.b) y J hJ
  have e₄ := r₄ (α + p.y) _ (add_right_comm α p.y p'.y) _ (𝟙 _) y J hJ
  have e₃ := r₃ α _ rfl _ (DegPre.trPt D F p'.g.b) y J hJ
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₁, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy] at e₂
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₃, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy, tr_comm] at e₄
  have t₁ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p'.g α p.y
  have t₂ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p.g α p'.y
  rw [hy] at t₁ t₂
  have t₃ := H _ (fst (TF (R := R) F) D.P.A) y J hJ
  obtain ⟨c, hc⟩ : ∃ c : ((DegPre.BF D F).left.presheaf.stalk y)ˣ, c.val =
      gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) :=
    ⟨_, (gs_unit _ y ⊤ trivial (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ)).symm⟩
  rw [← hc, ← Units.val_mul] at t₃
  have key := cub_comm C k _ _ _ (DegPre.prB D F) _ _ _ _ _ _ _ t₁ t₂ (Units.ext t₃)
  rw [sval_smul _ _ _ _ y hJ, Category.id_comp, ← hc, e₂, e₄, _root_.mul_assoc (sval _ _ _ _), _root_.mul_assoc (sval _ _ _ _),
    ← Units.val_mul, ← Units.val_mul, mul_left_comm c.val, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key' ⊢
  linear_combination (norm := abel) key'

theorem tr_inv (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul,
      inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phi {p : QkPt D F k} {w : Frm D F k p.g.b} {s t : Fam D F k} (h : PhiVal p w s.s t.s)
    (ht : ∀ β j, (t.s β).f j = 0) (α : D.X) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [tr_inv, UUA.sval_zero_of (ht _) _ y J (hJ.mem _ _)] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem weil_unique (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) (hk : 1 ≤ k) (p p' : QkPt D F k) {ζ ζ' : F}
    (h : WeilQkIs D F k p p' ζ) (h' : WeilQkIs D F k p p' ζ') : ζ = ζ' := by
  obtain ⟨w, hw⟩ : ∃ w : Frm D F k p.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨w', hw'⟩ : ∃ w : Frm D F k p'.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hk 0
  obtain ⟨s₁, r₁⟩ := exists_phi hG p' w' hw' hB s
  obtain ⟨s₂, r₂⟩ := exists_phi hG p w hw hB s₁
  obtain ⟨s₃, r₃⟩ := exists_phi hG p w hw hB s
  obtain ⟨s₄, r₄⟩ := exists_phi hG p' w' hw' hB s₃
  have a := fun {c : F} (h : WeilQkIs D F k p p' c) => (isSmul_iff _ _ _).1 (h w w' hw hw' s s₁ s₂ s₃ s₄
    ((phiRel_iff hG _ _ hw' _ _).2 r₁) ((phiRel_iff hG _ _ hw _ _).2 r₂) ((phiRel_iff hG _ _ hw _ _).2 r₃)
    ((phiRel_iff hG _ _ hw' _ _).2 r₄))
  have hne : s₄ ≠ 0 := fun h0 => (hs 0).2 ⟨0, by simp⟩
    (zero_of_phi r₃ (zero_of_phi r₄ fun β j => by rw [h0]; rfl) 0)
  exact smul_left_injective F hne ((a h).symm.trans (a h'))

theorem ratio_tor (p p' : QkPt D F k) (t : Multiplicative D.X →* Fˣ) (hy : p.y = 0) (ht : IsTor t p.g) {ζ : F}
    (H : IsRatio p p' ζ) : ζ = (t (Multiplicative.ofAdd p'.y)).val := by
  let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
  choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := H _ (𝟙 _) z J hJ
  have e₀ : val (p'.g.s p.y) (𝟙 _) z J = 1 := by
    rw [hy]; exact (val_corr hJ p'.g.s_zero _).trans (val_one _)
  have e₁ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p'.g.b) (𝟙 _ ≫ p.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact C.N_one _ _ _
  have e₂ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p.g.b) (𝟙 _ ≫ p'.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, Over.id_left, e₀, _root_.mul_one, _root_.mul_one, Units.val_one, _root_.mul_one, ht.2 _ z J hJ, _root_.GlobalTheory.UT.cst,
    gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at e
  exact ((((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙 (TF (R := R) F).left :
    (TF (R := R) F).left ⟶ _).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)).injective e).symm

end GlobalTheory.QkPairing

theorem GlobalTheory.weilQk_existsUnique : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  intro hL R _ _ _ I _ D F _ _ _ k hk p p'
  obtain ⟨ζ, hζ⟩ := GlobalTheory.QkPairing.exists_ratio p p'
  have hW := GlobalTheory.QkPairing.weil_of_ratio hL.1.globalFns p p' hζ
  refine ⟨⟨ζ, hW, fun ζ' h => Units.ext (GlobalTheory.QkPairing.weil_unique hL.1.globalFns hL.2.1.secTwist D.tau_bimult hk p p' h hW)⟩,
    fun t hy ht => ?_⟩
  rw [← GlobalTheory.QkPairing.ratio_tor p p' t hy ht hζ]; exact hW
end
end

