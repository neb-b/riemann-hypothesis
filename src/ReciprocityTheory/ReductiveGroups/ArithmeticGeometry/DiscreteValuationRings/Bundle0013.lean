module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenTerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtDone
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

theorem nuExt : NuExtSt :=
  nuExt_of fun _ _ _ _ _ hϖ _ _ hv _ _ _ hE _ hr f hf => secB_dvd_of_vge hϖ hv hE hr f hf

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section Move2

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem vge_move₂ {k₁ k₂ : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k₁))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k₁) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k₁) δ)
      (D.toPre.famφB χ) (DegPre.famε k₂))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k₁ α s r) : VGe D F v k₂ χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : D.toPre.SecB k₂ χ, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval t ρ z J = sval (σ i) (ρ ≫ TB) z J * (val eB ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) TB eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heB ρ z hJ)⟩
  choose σ' hσ' using e1
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k₂)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e2 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e2
  refine ⟨n, fun i => c * a i, σ', σ'F, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F i _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm ((r : ℚ) : WithTop ℚ)]
    exact add_le_add hq (hva i)
  · show s'.f j = ∑ i, resTop _ (gF D.toPre F (c * a i)) * (σ'F i).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have m := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' m
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have Ti : ∀ i, gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * (gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I) := fun i => by
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F i) (𝟙 _) y hy' m, hτ]
      exact mul_left_comm _ _ _
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ i, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Ti i
    have CORE : sval s' (𝟙 _) y I = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
      have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
      rw [H1, H2, hc y I hIy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
        rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
      have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I := by
        rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hh, Category.id_comp]
      have A3 : sval (σ'F i) (𝟙 _) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I *
          (val eB (DegPre.prB D.toPre F).left y I).val := by
        rw [hσ'F i _ (𝟙 _) y I hIy, Category.id_comp, hσ' i _ _ y I hIy]
      rw [A1, A2, A3, map_mul, gs_mul _ y ⊤ (by trivial)]
      ring
    exact T0.trans ((congrArg (fun x => τ * x) CORE).trans RHS.symm)

end Move2

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def PullGenStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (χ : D.toPre.X)
        (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))), u.IsGen →
        LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
          (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1)))
            (jFK (R := V) F)) →
        ∃ (m : ℕ) (ψ : Fin m → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (δ : Fin m → ℤ)
          (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)), eB.IsGen ∧
          FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) ψ)
            (Sum.elim (DegPre.famε k) δ) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) ∧
          ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧
            ∀ (y : (DegPre.BF D.toPre F).left)
              (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
              Good D.toPre.P.L y J →
              (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) *
                (val eB (DegPre.prB D.toPre F).left y J).val

def QAlStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (_oa : D.toPre.OAct O) (a : O) (N : ℕ),
      a * star a = (N : O) → star a * a = (N : O) → ∀ χ : D.toPre.X, Q (star a • χ) = N * Q χ

def PullbackValuationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v (k * N) s' r

private theorem fwd_lemma (hG : PullGenStatement) (hQ : QAlStatement) :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r → NuGe D Q F v (k * N) s' r := by
  intro V _ _ _ ϖ hϖ D Q hQD F _ _ v hv O _ _ _ oa w0 hw0 a N hN ha1 ha2 k hk s s' hpull r hs
  unfold NuGe at hs ⊢
  intro β
  obtain ⟨hrelAll, hzero⟩ := hpull
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, hcorr, hrel⟩ := hrelAll χ
    obtain ⟨m, ψ, δ, eB, heB, hform, c, hc0, hc⟩ :=
      hG V ϖ hϖ D F v hv O oa w0 hw0 a N hN ha1 ha2 k hk χ u hu hcorr
    have hfst : (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left =
        (fst (TF (R := V) F) D.toPre.P.A).left :=
      congrArg (fun φ => φ.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have hh : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
        (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
      congrArg (fun φ => φ.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have hq0 : ((0 : ℚ) : WithTop ℚ) ≤ v c := by simpa using hc0
    have key := SectionScalarValuation.vge_move₂ hfst hh u hrel eB heB hform c hc (q := 0) hq0 (hs χ)
    have hQa := hQ V ϖ hϖ D Q hQD O oa a N ha1 ha2 χ
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    convert key using 1
    rw [hQa]
    push_cast
    field_simp
    try ring
  · push_neg at hβ
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
    rw [hzero β hβ j]
    simp

def PullbackValuationForwardBound : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r → NuGe D Q F v (k * N) s' r

theorem pullback_valuation_forward_of (hG : PullGenStatement) (hQ : QAlStatement) : PullbackValuationForwardBound :=
  fwd_lemma hG hQ

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

def RepF {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))) (c : Fin m → F) : Prop :=
  ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
    sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J

theorem coordsO {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (σ : D.toPre.SecB k ρ) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hσF : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval σF (𝟙 _) y J = sval σ (DegPre.prB D.toPre F).left y J) :
    ∃ c : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ RepF bF σF c := by
  let bO := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TO hϖ hv) D.toPre.P.A).left
  have hBO := hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ
    (snd (TO hϖ hv) D.toPre.P.A).left)
  refine ⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩
  have e := sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd] at e
  rw [hσF y J hJ, e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have g := gs_jO hϖ hv (D := D) (𝟙 _) y (r i)
  rw [Category.id_comp] at g
  rw [g, hbF i y J hJ]
  show _ * sval (pullSec _ _ _ (b i) _) _ y J = _
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd]

theorem repF_unique {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    {bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))}
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c c' : Fin m → F}
    (h : RepF bF t c) (h' : RepF bF t c') : c = c' := by
  have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)),
      gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b :=
    fun y a b => gs_sub _ y ⊤ (by first | trivial | simp) a b
  have h0 := hU (c - c') (fun y J hy => by
    have e1 := h y J hy
    have e2 := h' y J hy
    simp only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFibre
section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]


set_option maxHeartbeats 1000000 in
theorem leading_expansion_term_ne_zero [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) (g : ∀ α, D.toPre.SecB 1 α) (hexp : U.ExpandsAt 0 1 s g)
    (hv : ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0) :
    ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g 0).f j) = 0 := by
  intro h0
  subst hI

  have hloc : ∀ {X : Scheme.{0}} {W : X.Opens} (y : Γ(X, W)),
      (∀ x ∈ W, ∃ V : X.Opens, ∃ hV : V ≤ W, x ∈ V ∧ (X.presheaf.map (homOfLE hV).op).hom y = 0) →
        y = 0 := by
    intro X W y h
    choose V hV hxV hy using h
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => V p.1 p.2) W
      (fun p => homOfLE (hV p.1 p.2)) ?_ y 0 ?_
    · intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    · intro p
      exact (hy p.1 p.2).trans (map_zero _).symm

  have hvan : ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι),
      ((U.gt 0).pG.left.app (D.toPre.P.L.wchart (D.toPre.famφB α) j)).hom ((g α).f j) = 0 := by
    intro α j
    have hz : ((pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0 := by
      by_cases hα : α = 0
      · subst hα
        exact h0 j
      · exact hv α hα j
    show (((U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0
    try rw [Scheme.comp_app]
    exact (congrArg (fun z => ((U.gt 0).q.left.app _).hom z) hz).trans (map_zero _)
  unfold NonzeroOnSpecial at hs
  obtain ⟨j, hj⟩ := hs
  obtain ⟨S, -, hS⟩ := hexp
  choose ch hch using fun y : D.toPre.P.A.left => WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB y
  apply hj
  refine hloc _ fun x hx => ?_
  refine ⟨U.expW 0 (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j S
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)),
    inf_le_left.trans inf_le_right, ?_, ?_⟩
  · refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨?_, ?_⟩, hx⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun _ => hch _
    · exact Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp hx 0
    · exact WeightPf.mem_finset_inf S _ x fun α _ => TopologicalSpace.Opens.mem_inf.mpr
        ⟨Set.mem_iInter.mpr fun i => hch _, Set.mem_iInter.mpr fun i => hch _⟩
  · have e := hS (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)) rfl (by
        intro a b hab
        rcases a with _ | a | a <;> rcases b with _ | b | b <;>
          exact congrArg (fun f => ch (f.base x)) hab)
    rw [Finset.sum_eq_zero (fun α _ => by rw [hvan, map_zero, zero_mul]), ← Units.val_pow_eq_pow_val] at e
    exact (Units.mul_right_eq_zero _).mp e

theorem generates_of_ne (hLaws : Laws) [IsDiscreteValuationRing R] (hI : I = maximalIdeal R)
    (t : D.toPre.SecB 1 0) (ht : ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ (t.f j) = 0) :
    SecBGenerates 1 0 t := by
  unfold SecBGenerates
  intro s'
  obtain ⟨c₀, c', h, h0⟩ := secB_rank_one (hLaws := hLaws) (t := t) (s' := s')
  haveI : Flat D.toPre.P.A.hom := flat_B

  have hc₀ : c₀ ≠ 0 := by
    intro hz
    apply ht
    intro j
    rw [h0 hz j, map_zero]

  have hdiv : ∃ a : R, c' = c₀ * a := by
    obtain ⟨m, hm | hm⟩ := ValuationRing.cond c₀ c'
    · exact ⟨m, hm.symm⟩
    · by_cases hmu : IsUnit m
      · obtain ⟨u, rfl⟩ := hmu
        refine ⟨↑u⁻¹, ?_⟩
        rw [← hm, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      · exfalso
        have hmI : m ∈ I ^ (0 + 1) := by
          rw [zero_add, pow_one, hI]
          exact (IsLocalRing.mem_maximalIdeal m).mpr hmu
        have hc' : c' ≠ 0 := by
          rintro rfl
          exact hc₀ (by rw [← hm, zero_mul])
        apply ht
        intro j
        have hj : t.f j = toW D.toPre.P.A.hom _ m * s'.f j := by
          refine (sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc' ?_)).symm
          rw [mul_sub, ← _root_.mul_assoc, ← map_mul, hm, h j, sub_self]
        rw [hj, map_mul, app_toW_of_mem D.toPre.P.A.hom (I ^ (0 + 1)) _ hmI, zero_mul]
  obtain ⟨a, rfl⟩ := hdiv
  have hSa : SecIsMul D.toPre.P.A.hom a s' t := by
    intro j
    rw [resTop_scal]
    refine sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc₀ ?_)
    rw [mul_sub, h j, map_mul, _root_.mul_assoc, sub_self]
  refine ⟨a, hSa, fun b hb => ?_⟩
  by_contra hne
  apply ht
  intro j
  have e1 := hb j
  have e2 := hSa j
  rw [resTop_scal] at e1 e2
  have hz : t.f j = 0 := by
    refine toW_mul_eq_zero D.toPre.P.A.hom _ (sub_ne_zero.mpr hne) ?_
    rw [map_sub, sub_mul, ← e1, ← e2, sub_self]
  rw [hz, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

