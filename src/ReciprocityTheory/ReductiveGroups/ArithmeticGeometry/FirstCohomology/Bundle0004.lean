module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.FinOrdExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

theorem finOrdExists_of (hΦ : DVR.PhiFunStatement) (hP : PhiPowStatement) : FinOrdExistsStatement := by
  intro V _ _ _ D F _ _ _ k hk p w hw
  obtain ⟨Φ, hΦr⟩ := hΦ V (maximalIdeal V) D F k hk p w hw
  obtain ⟨c, hc, hcp⟩ := hP V (maximalIdeal V) D F k hk p w hw
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (by omega : 0 < k)
  have hζc : ζ ^ k * c = 1 := by rw [hζ, inv_mul_cancel₀ hc]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hζc
    exact zero_ne_one hζc
  refine ⟨ζ, hζ0, k, hk, ?_⟩
  intro ss ts h

  have hpow : (Φ ^ k) (ss 0) = c • ss 0 := by
    have := hcp (fun i => (Φ ^ (i : ℕ)) (ss 0)) (by
      intro i
      rw [hΦr]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at this
    simpa using this
  have key : ∀ n : ℕ, (hn : n ≤ k) → ss ⟨n, by omega⟩ = ζ ^ n • (Φ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := h ⟨n, by omega⟩
      rw [hΦr] at h1
      rw [isSmul_iff] at h2
      have e : ss ⟨n + 1, by omega⟩ = ss (Fin.succ ⟨n, by omega⟩) := rfl
      have e0 : ss ⟨n, by omega⟩ = ss (Fin.castSucc ⟨n, by omega⟩) := rfl
      rw [e, h2, h1, ← e0, ih (by omega), LinearMap.map_smul, smul_smul, pow_succ' ζ n, pow_succ' Φ n,
        Module.End.mul_apply]
  have hlast : ss (Fin.last k) = ss 0 := by
    have := key k le_rfl
    have e : ss (Fin.last k) = ss ⟨k, by omega⟩ := rfl
    rw [e, this, hpow, smul_smul, hζc, one_smul]
  intro α j
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LocalResidues
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.H1.LocalResidues

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [Field k] {X W Z : Scheme.{0}}

theorem sval_rel {L : LB X} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ}
    (s s₀ : LB.Sec (LB.LinComb L φ ε)) (D : W.Opens) (rr : Γ(W, D))
    (hrel : ∀ j, (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s.f j) =
      (W.presheaf.map (homOfLE (inf_le_left : D ⊓ (LB.LinComb L φ ε).U j ≤ D)).op).hom rr *
      (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s₀.f j))
    (r : Z ⟶ W) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hz : r z ∈ D) :
    sval s r z J = gs r z D rr * sval s₀ r z J := by
  have hm : r z ∈ D ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (hrel (fun k => J (r ≫ φ k)))
  rw [gs_res r z _ hm, gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

end ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.TateTransport
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def TateTransportStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (Dw : Datum H),
    letI := H.starRing
    ∀ I₀ : TateIso Dw F (TF (R := R) F ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∃ I₁ : TateIso Dw F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
          (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c)),
        ∀ n, I₁.ζ n = I₀.ζ n

theorem weil_move (hW : WeilSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {φ : P.A.A.left ⟶ t.G.left} (hp : IsGrpPullback P.A.A t.G (jK R) φ)
    (w : LB.Iso P.A.L (t.PP.L.pull φ)) (hw : w.IsGen)
    (n : ℕ) (x y : TFK (R := R) F ⟶ P.A.A) (hx : x ^ n = 1) (hy : y ^ n = 1) (c : Γ(Sp F, ⊤)ˣ)
    (hG : WeilIs t.G t.PP.L n (pushPt hp.1.w x) (pushPt hp.1.w y) c) : WeilIs P.A.A P.A.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW (Sp (FractionRing R)) P.A n (TFK (R := R) F)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hsub : Subsingleton (Spec (CommRingCat.of F)) := inferInstance
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hsub q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (overRes (T := TF (R := R) F) V).hom = (overRes (T := TFK (R := R) F) V).hom ≫ jK R := by
    rw [Category.id_comp]; exact (Category.assoc _ _ _).symm
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n (overResι (T := TFK (R := R) F) V ≫ x) θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n (overResι (T := TFK (R := R) F) V ≫ y) θy₀ mvy
  have hm := commIsOf_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V) hp (𝟙 _) hτ t.PP.isLB P.A.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx)
    (by rw [hθy]; exact mvy) mx my (unitRes (T := TF (R := R) F) V c) (unitRes (T := TFK (R := R) F) V c) (fun Z r z => by rw [Category.comp_id]; rfl)
    (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := commIsOf_unique P.A.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem tateTransport_holds (hW : WeilSt) : TateTransportStatement := by
  intro E _ _ _ H R _ _ I t P F _ _ Dw
  letI := H.starRing
  intro I₀
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  obtain ⟨w, hw⟩ := hL
  let Φ := pushHom gpG (TFK (R := R) F)
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (gpG.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (gpG.1.lift x₀.left (jFK (R := R) F) (Over.w x₀)) (gpG.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gpG.1.lift_fst _ _ _)⟩
  let Φe : (TFK (R := R) F ⟶ P.A.A) ≃* (TF (R := R) F ⟶ t.G) := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦ : ∀ x, Φe x = pushPt gpG.1.w x := fun x => rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have hact : ∀ x a, Φe (x ≫ P.oA.act a) = Φe x ≫ t.act.act a := fun x a => by
    apply Over.OverMorphism.ext
    show (x ≫ P.oA.act a).left ≫ _ = (pushPt gpG.1.w x).left ≫ (t.act.act a).left
    rw [Over.comp_left, Category.assoc, actA]; rfl
  have hpow : ∀ n, 0 < n → ∀ a, (Φe.symm (I₀.ev n a)) ^ n = 1 := fun n hn a => by
    rw [← map_pow, (I₀.onto n hn _).2 ⟨a, rfl⟩, map_one]
  refine ⟨
    { ζ := I₀.ζ
      ζ_prim := I₀.ζ_prim
      ζ_pow := I₀.ζ_pow
      ev := fun n a => Φe.symm (I₀.ev n a)
      add := fun n a b => by simp only [I₀.add, map_mul]
      lin := fun n c a => by
        show Φe.symm (I₀.ev n (c • a)) = Φe.symm (I₀.ev n a) ≫ P.oA.act c
        apply Φe.injective
        rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
        exact I₀.lin n c a
      ker := fun n hn a => (map_eq_one_iff _ Φe.symm.injective).trans (I₀.ker n hn a)
      onto := fun n hn x => by
        rw [← map_eq_one_iff Φe Φe.injective, map_pow, I₀.onto n hn]
        exact exists_congr fun a => Φe.symm_apply_eq.symm
      tower := fun n m hn hm a => by rw [← map_pow, I₀.tower n m hn hm a]
      isom := fun n hn a b => by
        have h := I₀.isom n hn a b
        rw [← Φe.apply_symm_apply (I₀.ev n a), ← Φe.apply_symm_apply (I₀.ev n b), hΦ, hΦ] at h
        exact weil_move hW P F gpG w hw n _ _ (hpow n hn a) (hpow n hn b) _ h }, fun n => rfl⟩

end ReciprocityTheory.ChartRestriction.G.H1
end
end

