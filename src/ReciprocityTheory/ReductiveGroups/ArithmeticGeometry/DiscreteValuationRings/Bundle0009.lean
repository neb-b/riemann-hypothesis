module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem TF_hom : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
  simp only [TF, jFK, jK]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_liftO (b : TF (R := V) F ⟶ D.toPre.P.A) : ∃ m : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ m = b := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨x', hx'p, hx'⟩ := TWO.exists_lift v hϖ hv D.toPre.P.A.hom b.left (by rw [Over.w b, TF_hom])
  exact ⟨Over.homMk x' hx'p, Over.OverMorphism.ext hx'⟩

theorem liftO_unique (m₁ m₂ : TO hϖ hv ⟶ D.toPre.P.A) (h : ιS hϖ hv ≫ m₁ = ιS hϖ hv ≫ m₂) : m₁ = m₂ := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  apply Over.OverMorphism.ext
  exact TWO.lift_unique v hϖ hv D.toPre.P.A.hom m₁.left m₂.left (Over.w m₁) (Over.w m₂)
    (congrArg (fun g => g.left) h)

def gtφO (m : TO hϖ hv ⟶ D.toPre.P.A) (χ : D.toPre.X) : Fin 4 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(cP D.toPre _ χ * m).left, (cP D.toPre _ χ).left, m.left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left]

def lineφO (m : TO hϖ hv ⟶ D.toPre.P.A) : Fin 2 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(1 : TO hϖ hv ⟶ D.toPre.P.A).left, m.left]

def trO (m : TO hϖ hv ⟶ D.toPre.P.A) : TO hϖ hv ⊗ D.toPre.P.A ⟶ TO hϖ hv ⊗ D.toPre.P.A :=
  lift (fst _ _) (padd D.toPre.P.A (snd _ _) (fst _ _ ≫ m))

theorem trO_fst (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ fst _ _ = fst _ _ := by
  unfold trO
  exact lift_fst _ _

theorem trO_snd (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := by
  unfold trO
  rw [lift_snd]
  rfl

theorem jO_trO (b : TF (R := V) F ⟶ D.toPre.P.A) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = b) :
    jO hϖ hv (D := D) ≫ trO hϖ hv m = DegPre.trPt D.toPre F b ≫ jO hϖ hv := by
  have h1 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [trO_snd, MonObj.comp_mul, whiskerRight_snd, ← Category.assoc, whiskerRight_fst, Category.assoc, hm]
  have h2 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [whiskerRight_snd]
    unfold DegPre.trPt
    rw [lift_snd]
    rfl
  have h3 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [trO_fst, whiskerRight_fst]
  have h4 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [whiskerRight_fst, ← Category.assoc, tr_fst]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [h3, h4]
  · simp only [Category.assoc]
    rw [h1, h2]

theorem gen_uO (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by
  let a : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := cP D.toPre _ α
  let mm : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := fst _ _ ≫ m
  let x : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := snd _ _
  have hα' : cP D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A), hα]
    exact (map_mul (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D.toPre _ α) (map_pow (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.toPre.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.toPre.P.isLB (φ' := Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
      (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TO hϖ hv) D.toPre.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D.toPre (snd (TO hϖ hv) D.toPre.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D.toPre (trO hϖ hv m ≫ snd _ _) α k h
      have q₁ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α * m).left = (a * mm).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
          ((MonObj.comp_mul (fst (TO hϖ hv) D.toPre.P.A) (cP D.toPre _ α) m).trans
            (congrArg (· * mm) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)))
      have q₂ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α).left = a.left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)
      have q₃ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left =
          (1 : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (fst (TO hϖ hv) D.toPre.P.A))
      have q₄ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trO_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ N (LB.invGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (thφ D.toPre.P.A (x3 D.toPre.P.A)) thε D.toPre.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.toPre.P.L _ _ vO (fst (TO hϖ hv) D.toPre.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.toPre.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D.toPre ρ α]

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem app_fst_eq_zero_of_snd {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ((pullback.snd t p).app W).hom d = 0) : ((pullback.fst p t).app W).hom d = 0 := by
  rw [← CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd, AlgebraicGeometry.Scheme.Hom.comp_app]
  erw [CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem snd_app_eq_zero {X T S : Scheme.{0}} (p : X ⟶ S) (t : T ⟶ S) (W : X.Opens) (d : Γ(X, W))
    (h : ∀ y : ↥(CategoryTheory.Limits.pullback t p : Scheme.{0}), CategoryTheory.Limits.pullback.snd t p y ∈ W → gs (CategoryTheory.Limits.pullback.snd t p) y W d = 0) :
    ((CategoryTheory.Limits.pullback.snd t p).app W).hom d = 0 := by
  refine TopCat.Presheaf.section_ext (CategoryTheory.Limits.pullback t p).sheaf _ _ _ fun y hy => ?_
  have hy' : CategoryTheory.Limits.pullback.snd t p y ∈ W := hy
  have := h y hy'
  simp only [gs, dif_pos hy'] at this
  erw [this]
  exact (map_zero _).symm

theorem secB_dvd_of_vge {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {D : Out.DegData V (IsLocalRing.maximalIdeal V)}
    {vK : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) vK) {k : ℕ}
    {α : D.toPre.X}
    {E : LB.Sec (LB.LinComb D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k))}
    (hE : VGe D (FractionRing V) vK k α E 0) {r : V} (hr : r ≠ 0) (f : D.toPre.SecB k α)
    (hf : Out.GeneratorPullback.SecScal D.toPre.P.L (Out.DegPre.famφ D.toPre (FractionRing V) α) (Out.DegPre.famε k) E
      (D.toPre.famφB α) (Out.DegPre.famε k) f (Out.DegPre.prB D.toPre (FractionRing V)).left
      (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r)) :
    ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      f.f j = Geo.Tor.constFn D.toPre.P.A.hom _ r * g := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hE
  have hb : ∀ i, ∃ b : V, algebraMap V (FractionRing V) b = a i := fun i => by
    obtain ⟨b, hb⟩ := mem_range_of_val_nonneg hϖ hv (a i) (by simpa using hva i)
    exact ⟨b, hb⟩
  choose b hb using hb
  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim
    have := SmoothOfRelativeDimension.smooth D.toPre.P.g D.toPre.P.A.hom
    infer_instance
  have hjK : IsOpenImmersion (jK V) := by
    obtain ⟨ϖ₀, h₀⟩ := IsDiscreteValuationRing.exists_irreducible V
    have := away_fractionRing h₀
    exact IsOpenImmersion.of_isLocalization ϖ₀
  have hjFK : IsIso (jFK (R := V) (FractionRing V)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id (FractionRing V))))
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have ht : IsOpenImmersion (TF (R := V) (FractionRing V)).hom := by
    show IsOpenImmersion (jFK (R := V) (FractionRing V) ≫ jK V)
    infer_instance
  have : Nonempty (TF (R := V) (FractionRing V)).left := ⟨IsLocalRing.closedPoint (FractionRing V)⟩

  have hBF : (Out.DegPre.BF D.toPre (FractionRing V)).hom =
      pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom ≫ D.toPre.P.A.hom := pullback.condition
  have hnat : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) (x : R),
      (Spec.map g).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (g.hom x) := by
    intro R S g x
    exact (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality g)).symm
  have hTF : ∀ c : V, (TF (R := V) (FractionRing V)).hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) := by
    intro c
    show (jFK (R := V) (FractionRing V) ≫ jK V).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat, hnat]
    rfl

  have H : ∀ j : (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).ι,
      f.f j - constFn D.toPre.P.A.hom _ r * ∑ i, constFn D.toPre.P.A.hom _ (b i) * (σ i).f j = 0 := by
    intro j
    refine eq_zero_of_app_fst_open D.toPre.P.A.hom (TF (R := V) (FractionRing V)).hom _ _
      (app_fst_eq_zero_of_snd _ _ _ _ (snd_app_eq_zero _ _ _ _ fun y hy => ?_))
    choose J hJ using fun ψ : (Out.DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ y)
    have hG : Good D.toPre.P.L y J := hJ
    set π := pullback.snd (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom
    set U := (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (Out.DegPre.famε k)).U j
    obtain ⟨tj, htj⟩ : ∃ tj, (trF (L := D.toPre.P.L) (D.toPre.famφB α) (Out.DegPre.famε k) π y j
        (fun k => J (π ≫ D.toPre.famφB α k))).val = tj := ⟨_, rfl⟩
    have e_f : gs π y U (f.f j) = tj * sval f π y J :=
      (sec_trans f π y hy (hG.mem _ π)).trans (congrArg (· * sval f π y J) htj)
    have e_σ : ∀ i, gs π y U ((σ i).f j) = tj * sval (σ i) π y J := fun i =>
      (sec_trans (σ i) π y hy (hG.mem _ π)).trans (congrArg (· * sval (σ i) π y J) htj)
    have hf' : sval f (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) *
        sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := secScal_sval_c hf (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have hσ' : ∀ i, sval (σ i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) ≫ π) y J = sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J := fun i =>
      SectionScalarValuation.secScal_sval (hscal i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    rw [Category.id_comp] at hf'
    simp only [Category.id_comp] at hσ'
    let bg : Fin n → Γ((pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom), ⊤) := fun i =>
      (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (a i))
    have hE' : sval E (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J = ∑ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) * sval (σF i) (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y J :=
      SectionScalarValuation.sval_lin bg σF hsum (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y hG
    have c1 : gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (Out.scal (Out.DegPre.BF D.toPre (FractionRing V)).hom r) = cst (π ≫ D.toPre.P.A.hom) y r :=
      (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans (by rw [Category.id_comp, hBF]; rfl)
    have c2 : ∀ i, gs (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) y ⊤ (bg i) = cst (π ≫ D.toPre.P.A.hom) y (b i) := by
      intro i
      refine (gs_pull (𝟙 (pullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom)) _ y ⊤ trivial _).trans ?_
      rw [Category.id_comp, cst, ← pullback.condition, ← gs_pull _ _ y ⊤ trivial]
      exact (congrArg (fun z => gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom z)) (hb i).symm).trans
        (congrArg (gs (pullback.fst (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom) y ⊤) (hTF (b i)).symm)
    have e_sub : gs π y U (f.f j - constFn D.toPre.P.A.hom U r * ∑ i, constFn D.toPre.P.A.hom U (b i) * (σ i).f j) =
        gs π y U (f.f j) - gs π y U (constFn D.toPre.P.A.hom U r) *
          ∑ i, gs π y U (constFn D.toPre.P.A.hom U (b i)) * gs π y U ((σ i).f j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [gs_eq π y U hy, map_sub, map_mul, map_sum]
    rw [e_sub, e_f, hf', hE', gs_constFn _ _ _ _ hy]
    simp only [e_σ, hσ', c1, c2, gs_constFn _ _ _ _ hy]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  intro j
  exact ⟨_, sub_eq_zero.1 (H j)⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section FamPr

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R}

theorem famφB_pr (pD : IsPowDeg D' D j) (α' : D'.X) (i : Fin j) (a : Fin 4) :
    D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a := by
  haveI := pD.pw.hom i
  have hc := pD.c_pr α' i
  fin_cases a <;>
    simp [DegPre.famφB, ← Over.comp_left, padd, hc, IsMonHom.mul_hom, IsMonHom.one_hom]
  all_goals
    first
    | (rw [← Over.comp_left]; congr 1;
        simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])
    | (congr 1; simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])

def boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) (α' : D'.X) : D'.SecB k α' :=
  secOfIso (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _)

theorem isBoxFamB_boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) :
    IsBoxFamB pD k (boxFamB pD k f) f := by
  intro α'
  refine ⟨famφB_pr pD α', fun jN jM => ?_⟩
  set V := LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓ LB.wchart D'.P.L (D'.famφB α') jM with hVdef
  have hVab : V ≤ LB.wchart D'.P.L (D'.famφB α') jM ⊓ LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN :=
    fun _ hy => ⟨hy.2, hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _) jM jN)
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) jM jN hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (boxLB D.P.L pD.pw.pr) (D'.famφB α') (DegPre.famε k))
      (LB.LinComb D'.P.L (D'.famφB α') (DegPre.famε k))).U (jN, jM) := fun _ hy => ⟨hy.1, hy.2⟩
  have hu : res hVd ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) =
      @id (Γ(D'.P.A.left, V)ˣ) ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) :=
    res_refl' _
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((D'.P.A.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

end FamPr

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

section Values

variable {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem tau_nsmul (hB : D.TauBimult) (ρ mu nu : D.X) (k : ℕ) :
    val (D.tau (ρ + k • mu) nu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      val (D.tau ρ nu) (σ.left ≫ jFK (R := R) F) z J * val (D.tau mu nu) (σ.left ≫ jFK (R := R) F) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := tau_mul σ hJ hB (ρ + k • mu) mu nu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, pow_succ]
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e
    have a2 := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow, cubN] at a1 a2 ⊢
    linear_combination (norm := abel) a1 + a2

theorem psi_add (a b : D.X) : val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J =
    val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.psi a) (σ.left ≫ jFK (R := R) F) z J *
      val (D.psi b) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Values

theorem val_powGen' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

theorem fe_cocycle (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (ρ' : T ⟶ DegPre.BF D F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (ρ mu nu : D.X) :
    (uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J *
        val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J) *
      (uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J * val (DegPre.famMult D F k nu (ρ + k • mu)) (ρ' ≫ fst _ _).left z J) =
    uVal D F k ρ (cP D _ (mu + nu)) ρ' z J * val (DegPre.famMult D F k (mu + nu) ρ) (ρ' ≫ fst _ _).left z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have hf : (ρ' ≫ DegPre.trF D F nu) ≫ fst (TF (R := R) F) D.P.A = ρ' ≫ fst _ _ := by
    rw [Category.assoc, trF_eq, tr_fst]
  have hp : (ρ' ≫ DegPre.trF D F nu) ≫ DegPre.prB D F = (ρ' ≫ DegPre.prB D F) * cP D T nu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ← Category.assoc, comp_cP]
  have hc : ∀ χ, ρ' ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ χ = cP D T χ := fun χ => by
    rw [← Category.assoc, comp_cP]
  have u1 : uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu) ((ρ' ≫ DegPre.prB D F) * cP D T nu) := by
    rw [uVal, hp, ← Category.assoc (ρ' ≫ DegPre.trF D F nu), hf, Category.assoc, hc]; rfl
  have u2 : uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J =
      hv (th D z J) k (cP D T ρ * cP D T mu ^ k) (cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add, cPoint_nsmul]; rfl
  have u3 : uVal D F k ρ (cP D _ (mu + nu)) ρ' z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu * cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add]; rfl
  have hvc := hv_comp C k (cP D T ρ) (cP D T mu) (cP D T nu) (ρ' ≫ DegPre.prB D F)
  have σσ := ρ' ≫ fst (TF (R := R) F) D.P.A
  have fM : ∀ ν α, val (DegPre.famMult D F k ν α) (ρ' ≫ fst _ _).left z J =
      val (D.tau ν α) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J *
        (val (D.psi ν) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k *
          val D.rigK ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k) := fun ν α => by
    rw [val_famMult (ρ' ≫ fst _ _) hJ k ν α, val_powGen', val_powGen']
  have t1 := tau_mul (ρ' ≫ fst _ _) hJ hB mu nu ρ
  have t2 := tau_nsmul (ρ' ≫ fst _ _) hJ hB ρ mu nu k
  have t3 := tau_symm (ρ' ≫ fst _ _) hJ nu (ρ + k • mu)
  have t4 := tau_symm (ρ' ≫ fst _ _) hJ ρ nu
  have p1 := psi_add (ρ' ≫ fst _ _) hJ mu nu
  have sy : th D z J (cP D T ρ) (cP D T nu) (cP D T mu) = th D z J (cP D T mu) (cP D T nu) (cP D T ρ) := by
    rw [C.s01, C.s12, C.s01]
  have h8 : hv (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) * (th D z J (cP D T ρ) (cP D T nu) (cP D T mu))⁻¹ := rfl
  rw [u1, u2, u3, fM, fM, fM]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg (fun q => (k : ℕ) • Additive.ofMul q) p1
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  have a5 := congrArg Additive.ofMul t3
  have a6 := congrArg Additive.ofMul t4
  have a7 := congrArg Additive.ofMul sy
  have a8 := congrArg Additive.ofMul h8
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, smul_add] at a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  linear_combination (norm := abel) a1 - a2 - a3 + a4 + a5 + a6 - a7 + a8

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

