module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.ActPull

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

section Join

variable {X X' Y Y' : Scheme.{0}}

theorem isGen_part {N : LB X} {N' : LB X'} {M : LB Y} {M' : LB Y'} {e : Y ⟶ X} {e' : Y' ⟶ X'} {π : N.ι → M.ι}
    {π' : N'.ι → M'.ι} (h : IsPart N M e π) (h' : IsPart N' M' e' π') {Φ : X' ⟶ X} {Ψ : Y' ⟶ Y}
    (sq : e' ≫ Φ = Ψ ≫ e) (w : LB.Iso N' (N.pull Φ)) {v : LB.Iso M' (M.pull Ψ)} (hv : v.IsGen)
    (H : ∀ (x : Y') p q, Ψ x ∈ M.U (π p) → x ∈ M'.U (π' q) → gw w (𝟙 _ ≫ e') x p q = gw v (𝟙 _) x (π p) (π' q))
    (a b : (LB.div (N.pull Φ) N').ι) (x : Y')
    (hx : e' x ∈ (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b) :
    gm e' x _ (res (inf_le_left : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s a)) =
      gm e' x _ ((LB.div (N.pull Φ) N').g a b *
        res (inf_le_right : (LB.div (N.pull Φ) N').U a ⊓ (LB.div (N.pull Φ) N').U b ≤ _) (w.s b)) := by
  obtain ⟨J, k⟩ := a
  obtain ⟨J', k'⟩ := b
  have pt : Φ (e' x) = e (Ψ x) := congrArg (fun q : Y' ⟶ X => q x) sq
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have mj := (h.mem _ _).1 (pt ▸ hj)
  have mj' := (h.mem _ _).1 (pt ▸ hj')
  have mk := (h'.mem _ _).1 hx.1.2
  have mk' := (h'.mem _ _).1 hx.2.2
  have e₀ := (isGen_iff v).1 hv _ (𝟙 _) x _ _ _ _ mj mj' mk mk'
  rw [← H x _ _ mj mk, ← H x _ _ mj' mk', ← h.g _ (𝟙 _ ≫ Ψ) x _ _ mj mj', ← h'.g _ (𝟙 _) x _ _ mk mk',
    Category.id_comp, Category.id_comp, ← sq, ← gm_div_g e' x _ _ k k' hj hj' hx.1.2 hx.2.2] at e₀
  exact (gm_res _ x _ hx _).trans (e₀.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {X₁ X₂ X₁' X₂' : Scheme.{0}} {M₁ : LB X₁} {M₂ : LB X₂} {M₁' : LB X₁'} {M₂' : LB X₂'} {Φ₁ : X₁' ⟶ X₁}
  {Φ₂ : X₂' ⟶ X₂}

theorem exists_join_iso {w₁ : LB.Iso M₁' (M₁.pull Φ₁)} {w₂ : LB.Iso M₂' (M₂.pull Φ₂)} (h₁ : w₁.IsGen) (h₂ : w₂.IsGen) :
    ∃ w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J', Good (join M₁ M₂) z J → Good (join M₁' M₂') z J' →
        (∀ ψ, om w z J J' (ψ ≫ coprod.inl) = om w₁ z (rl J) (rl J') ψ) ∧
        ∀ ψ, om w z J J' (ψ ≫ coprod.inr) = om w₂ z (rr J) (rr J') ψ := by
  have s₁ : coprod.inl ≫ coprod.map Φ₁ Φ₂ = Φ₁ ≫ coprod.inl := coprod.inl_map _ _
  have s₂ : coprod.inr ≫ coprod.map Φ₁ Φ₂ = Φ₂ ≫ coprod.inr := coprod.inr_map _ _
  have p₁ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inl : X₁' ⟶ _) x) = (coprod.inl : X₁ ⟶ _) (Φ₁ x) :=
    fun x => congrArg (fun q : X₁' ⟶ X₁ ⨿ X₂ => q x) s₁
  have p₂ : ∀ x, coprod.map Φ₁ Φ₂ ((coprod.inr : X₂' ⟶ _) x) = (coprod.inr : X₂ ⟶ _) (Φ₂ x) :=
    fun x => congrArg (fun q : X₂' ⟶ X₁ ⨿ X₂ => q x) s₂
  choose a ha₁ ha₂ using fun i : (LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).ι =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) (join M₁' M₂')).U i)
      ((M₁.pull Φ₁).U (fun _ => (i.1 PUnit.unit).1) ⊓ M₁'.U i.2.1)
      ((M₂.pull Φ₂).U (fun _ => (i.1 PUnit.unit).2) ⊓ M₂'.U i.2.2)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inl _ _ _).1 (p₁ x ▸ mem_pull.1 hx.1)), (mem_jU_inl _ _ _).1 hx.2⟩)
      (fun x hx => ⟨mem_pull.2 ((mem_jU_inr _ _ _).1 (p₂ x ▸ mem_pull.1 hx.1)), (mem_jU_inr _ _ _).1 hx.2⟩)
      (w₁.s (fun _ => (i.1 PUnit.unit).1, i.2.1)) (w₂.s (fun _ => (i.1 PUnit.unit).2, i.2.2))
  let w : LB.Iso (join M₁' M₂') ((join M₁ M₂).pull (coprod.map Φ₁ Φ₂)) := ⟨a⟩
  have v₁ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₁ (ψ z) ∈ M₁.U p.1 → ψ z ∈ M₁'.U q.1 → gw w (ψ ≫ coprod.inl) z p q = gw w₁ ψ z p.1 q.1 :=
    fun Z ψ z p q hp hq => ha₁ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₁ (ψ z)).symm ▸ (mem_jU_inl _ _ _).2 hp), (mem_jU_inl _ _ _).2 hq⟩
  have v₂ : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂') (z : Z) (p : (join M₁ M₂).ι) (q : (join M₁' M₂').ι),
      Φ₂ (ψ z) ∈ M₂.U p.2 → ψ z ∈ M₂'.U q.2 → gw w (ψ ≫ coprod.inr) z p q = gw w₂ ψ z p.2 q.2 :=
    fun Z ψ z p q hp hq => ha₂ (fun _ => p, q) Z ψ z
      ⟨mem_pull.2 ((p₂ (ψ z)).symm ▸ (mem_jU_inr _ _ _).2 hp), (mem_jU_inr _ _ _).2 hq⟩
  refine ⟨w, fun i j => unit_ext_coprod
    (isGen_part (isPart_inl M₁ M₂) (isPart_inl M₁' M₂') s₁ w h₁ (fun x => v₁ _ (𝟙 _) x) i j)
    (isGen_part (isPart_inr M₁ M₂) (isPart_inr M₁' M₂') s₂ w h₂ (fun x => v₂ _ (𝟙 _) x) i j),
    fun Z z J J' hJ hJ' => ⟨fun ψ => ?_, fun ψ => ?_⟩⟩
  · have e : (ψ ≫ coprod.inl) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₁) ≫ coprod.inl := by
      rw [Category.assoc, s₁, Category.assoc]
    rw [om, e]
    exact v₁ Z ψ z _ _ ((isPart_inl M₁ M₂).good hJ (ψ ≫ Φ₁)) ((isPart_inl M₁' M₂').good hJ' ψ)
  · have e : (ψ ≫ coprod.inr) ≫ coprod.map Φ₁ Φ₂ = (ψ ≫ Φ₂) ≫ coprod.inr := by
      rw [Category.assoc, s₂, Category.assoc]
    rw [om, e]
    exact v₂ Z ψ z _ _ ((isPart_inr M₁ M₂).good hJ (ψ ≫ Φ₂)) ((isPart_inr M₁' M₂').good hJ' ψ)

end Join

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nrm_unique {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {x : D₁.X} {y : D₂.X} {u u' : LB.Gen (CmpLB D₁ D₂ a x y)}
    (hu : Nrm u) (hu' : Nrm u') (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J) (hJ : Good (JN D₁ D₂) z J) :
    val u r z J = val u' r z J :=
  gen_unique (jn_isLB D₁ D₂) D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A]) (GlobalTheory.globalFns_holds _ _ D₁.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => by
      have e := (hu.2 _ (𝟙 _) y J hJ).trans (hu'.2 _ (𝟙 _) y J hJ).symm
      rwa [Category.id_comp] at e) Z r z J hJ

theorem act_iff_of_nrm {D₁ D₂ : DegPre R} {a : D₁.P.A ⟶ D₂.P.A} {h : D₂.X →+ D₁.X}
    (u : ∀ χ, LB.Gen (CmpLB D₁ D₂ a (h χ) χ)) (hu : ∀ χ, Nrm (u χ)) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : GtPtF D₁ F) (g' : GtPtF D₂ F) : Act D₁ D₂ a h g g' ↔ g'.b = g.b ≫ a ∧ ∀ χ z J, Good (JN D₁ D₂) z J →
      val (g'.s χ) (𝟙 _) z (rr J) = val (g.s (h χ)) (𝟙 _) z (rl J) * val (u χ) g.b.left z J :=
  and_congr_right fun _ => forall_congr' fun χ => ⟨fun H => H _ (hu χ), fun H _ hv z J hJ =>
    (H z J hJ).trans (congrArg _ (nrm_unique (hu χ) hv _ _ z J hJ))⟩

theorem prod_Oε (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ k, h (D.Oφ p x k) ^ Oε k = (∏ k, h (D.Oφ p x k) ^ Oinvε k)⁻¹ := by
  rw [OLinEnd.prod_Oφ, OLinEnd.prod_Oφ_inv D p]
  simp only [mul_inv, inv_inv]

variable {φ : R →+* R'} {D₁ D₂ : DegPre R} {D₁' D₂' : DegPre R'} (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂')

theorem exists_u {a : D₁.P.A ⟶ D₂.P.A} {a' : D₁'.P.A ⟶ D₂'.P.A} [IsMonHom a']
    (ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left) {x : D₁.X} (x' : D₁'.X) (y' : D₂'.X) (hx : hD₁.xe x' = x)
    (u : LB.Gen (CmpLB D₁ D₂ a x (hD₂.xe y'))) (hu : Nrm u) :
    ∃ u' : LB.Gen (CmpLB D₁' D₂' a' x' y'), Nrm u' ∧
      ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
        Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
          (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
            (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' := by
  subst hx
  obtain ⟨w, hw, vw⟩ := exists_join_iso hD₁.w_gen hD₂.w_gen
  obtain ⟨u', hu', vu⟩ := exists_down_om hw (jn_isLB D₁ D₂) (jn_isLB D₁' D₂')
    (φ' := Sum.elim (fun k => D₁'.Oφ (𝟙 _) x' k ≫ coprod.inl) (fun k => D₂'.Oφ a' y' k ≫ coprod.inr)) (proj hD₁) (by
      rintro (k | k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inl_map, ← Category.assoc]
        exact congrArg (· ≫ _)
          (TorusCoordPull.Oφ_pull hD₁ (𝟙 _) (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm) x' k)
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _))
        rw [coprod.inr_map, ← Category.assoc]
        exact congrArg (· ≫ _) (TorusCoordPull.Oφ_pull hD₂ a a' _ ha y' k)) u hu.1
  have key : ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D₁'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
      Good (JN D₁ D₂) z J → Good (JN D₁' D₂') z J' → val u ((r ≫ p.left) ≫ proj hD₁) z J =
        (∏ k, om hD₁.w z (rl J) (rl J') (r ≫ D₁'.Oφ p x' k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w z (rr J) (rr J') (r ≫ D₂'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' :=
    fun T p Z r z J J' hJ hJ' => by
    refine (vu Z (r ≫ p.left) z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    obtain ⟨o₁, o₂⟩ := vw Z z J J' hJ hJ'
    rw [Fintype.prod_sum_type, ← prod_Oε D₁' p x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q))]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oε k) ?_)
      (Finset.prod_congr rfl fun k _ => congrArg (· ^ Oinvε k) ?_)
    · refine Eq.trans (congrArg _ ?_) (o₁ _)
      rw [Sum.elim_inl, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp, Category.comp_id]
    · refine Eq.trans (congrArg _ ?_) (o₂ _)
      rw [Sum.elim_inr, ← Category.assoc, Category.assoc r, WeightPf.Oφ_comp]
  refine ⟨u', ⟨hu', fun Z r z J' hJ' => ?_⟩, key⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) z
  have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁'.P.A).left = eSec D₁'.P.A := Category.id_comp _
  have z₀ : ∀ (D : DegPre R') (T : Over (Spec (CommRingCat.of R'))) (χ : D.X) {U : Type} [CommGroup U]
      (f : (T.left ⟶ D.P.A.left) → U), ∏ k, f (D.Oφ (1 : T ⟶ D.P.A) χ k) ^ Oinvε k = 1 := fun D T χ U _ f => by
    rw [OLinEnd.prod_Oφ_inv, _root_.mul_one]; simp
  have e := key (𝟙_ (Over (Sp R'))) 1 Z r z J J' hJ hJ'
  rw [MonObj.one_comp, o₁] at e
  have e₁ : val u ((r ≫ eSec D₁'.P.A) ≫ proj hD₁) z J = 1 := by
    rw [Category.assoc, hD₁.he, ← Category.assoc]
    exact hu.2 Z _ z J hJ
  have e₂ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) (congrArg₂ (fun a b => a⁻¹ * b)
    (z₀ D₁' (𝟙_ (Over (Sp R'))) x' (fun q => om hD₁.w z (rl J) (rl J') (r ≫ q)))
    (z₀ D₂' (𝟙_ (Over (Sp R'))) y' (fun q => om hD₂.w z (rr J) (rr J') (r ≫ q)))) rfl))
  rw [inv_mul_cancel, _root_.one_mul] at e₂
  exact e₂.symm

theorem main : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  intro R R' _ _ _ _ φ D₁ D₂ D₁' D₂' hD₁ hD₂ a h a' h' _ _ hb hx hu F _ _ _ g₁ g₂ g₁' g₂' h₁ h₂
  have ha : a'.left ≫ proj hD₂ = proj hD₁ ≫ a.left := by
    rw [← Category.assoc, ← Over.comp_left, hb, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
  choose u hu using hu
  choose u' hu' vu using fun χ => exists_u hD₁ hD₂ ha (h' χ) χ (hx χ) (u (hD₂.xe χ)) (hu _)
  rw [act_iff_of_nrm u hu, act_iff_of_nrm u' hu']
  have hb : (g₁'.b ≫ a').left ≫ proj hD₂ = (g₁.b ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc]
    exact congrArg (· ≫ _) h₁.1
  have hiff : g₂.b = g₁.b ≫ a ↔ g₂'.b = g₁'.b ≫ a' :=
    ⟨fun H => ext_of_iso_pullback _ hD₂.e (h₂.1.trans ((congrArg (·.left) H).trans hb.symm)),
      fun H => Over.OverMorphism.ext (h₂.1.symm.trans ((congrArg (·.left ≫ proj hD₂) H).trans hb))⟩
  rw [hiff]
  refine and_congr_right fun H => ?_
  have key : ∀ χ (y : Sp F) J J', Good (JN D₁ D₂) y J → Good (JN D₁' D₂') y J' →
      (vS (g₂.s (hD₂.xe χ)) y (rr J) = vS (g₁.s (h (hD₂.xe χ))) y (rl J) * val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J ↔
        vS (g₂'.s χ) y (rr J') = vS (g₁'.s (h' χ)) y (rl J') * val (Z := Sp F) (u' χ) g₁'.b.left y J') := by
    intro χ y J J' hJ hJ'
    have e₁ : vS (g₁.s (hD₁.xe (h' χ))) y (rl J) =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k) * vS (g₁'.s (h' χ)) y (rl J') :=
      (pullGt_val hD₁ h₁ (h' χ) (𝟙 _) ((isPart_inl _ _).good hJ) ((isPart_inl _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₁' g₁'.b (h' χ) (fun q => om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₂ : vS (g₂.s (hD₂.xe χ)) y (rr J) =
        (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) * vS (g₂'.s χ) y (rr J') := by
      rw [← H]
      exact (pullGt_val hD₂ h₂ χ (𝟙 _) ((isPart_inr _ _).good hJ) ((isPart_inr _ _).good hJ')).trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D₂' g₂'.b χ (fun q => om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₃ : val (Z := Sp F) (u (hD₂.xe χ)) g₁.b.left y J =
        (∏ k, om hD₁.w y (rl J) (rl J') (𝟙 (Sp F) ≫ D₁'.Oφ g₁'.b (h' χ) k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD₂.w y (rr J) (rr J') (𝟙 (Sp F) ≫ D₂'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) *
          val (Z := Sp F) (u' χ) g₁'.b.left y J' :=
      (congrArg (fun q => val (Z := Sp F) (u (hD₂.xe χ)) q y J)
        ((congrArg (· ≫ proj hD₁) (Category.id_comp _)).trans h₁.1).symm).trans
        ((vu χ _ g₁'.b (Sp F) (𝟙 _) y J J' hJ hJ').trans (congrArg₂ (· * ·) rfl
          (congrArg (fun q => val (Z := Sp F) (u' χ) q y J') (Category.id_comp _))))
    rw [hx] at e₁
    rw [e₁, e₂, e₃]
    exact EndBaseChange.cancel_iff _ _ _ _ _
  constructor
  · intro H χ y J' hJ'
    obtain ⟨J, hJ⟩ := DegPull.exists_good' (jn_isLB D₁ D₂) (Z := Sp F) y
    exact (key χ y J J' hJ hJ').1 (H _ y J hJ)
  · intro H χ y J hJ
    obtain ⟨χ, rfl⟩ := hD₂.xe.surjective χ
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' (jn_isLB D₁' D₂') (Z := Sp F) y
    exact (key χ y J J' hJ hJ').2 (H _ y J' hJ')

end GlobalTheory.Mum.Two.ActPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarRescaleDegreeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Rescale

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (g z) ∈ U)
    (a : Γ(X, U)) : gs (g ≫ f) z U a = (g.stalkMap z).hom (gs f (g z) U a) := by
  rw [gs_stalkMap (g ≫ f) z U h, gs_stalkMap f (g z) U h, Scheme.Hom.stalkMap_comp]
  rfl

theorem cst_zero' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 0 = 0 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (q : Y ⟶ Sp V) (r : Z ⟶ Y) (z : Z) (a : V) :
    gs r z ⊤ (scal q a) = cst (r ≫ q) z a :=
  gs_pull r q z ⊤ trivial _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem cancel (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (hα : Flat C.α) (b : W) (hb : b ≠ 0) (s₁ : SecK C.P.L.L T.β 1) (s₂ : SecK C.P.L.L C.α 1)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → cst (p ≫ T.G.hom) z b * sval s₁ p z J = cst (p ≫ T.G.hom) z b * sval s₂ p' z J)
    (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (hp : p ≫ T.β = p' ≫ C.α) (z : Z)
    (J : (Z ⟶ C.G.left) → C.P.L.L.ι) (hJ : Good C.P.L.L z J) : sval s₁ p z J = sval s₂ p' z J := by
  haveI := T.U.smooth
  haveI : Flat (pullback.fst T.β C.α ≫ T.G.hom) := inferInstance
  obtain ⟨g, rfl, rfl⟩ : ∃ g, g ≫ pullback.fst T.β C.α = p ∧ g ≫ pullback.snd T.β C.α = p' :=
    ⟨pullback.lift p p' hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good C.P.L.L C.P.L.isLB (g z) (K := Unit)
    (fun _ => pullback.fst T.β C.α ≫ T.β) (fun _ => J ((g ≫ pullback.fst T.β C.α) ≫ T.β)) (fun _ _ _ => rfl)
    (fun _ => hJ ((g ≫ pullback.fst T.β C.α) ≫ T.β))
  have key := h _ (pullback.fst T.β C.α) (pullback.snd T.β C.α) pullback.condition (g z) J₀ hJ₀
  have eJ : J₀ (pullback.snd T.β C.α ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) :=
    congrArg J₀ pullback.condition.symm
  have A₁ : sval s₁ (g ≫ pullback.fst T.β C.α) z J = (g.stalkMap z).hom (sval s₁ (pullback.fst T.β C.α) (g z) J₀) := by
    rw [sval_of s₁ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => (e₀ ()).symm),
      sval_of s₁ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => rfl)]
    exact gs_comp_stalk g _ z _ (hJ₀.mem _ _) _
  have A₂ : sval s₂ (g ≫ pullback.snd T.β C.α) z J = (g.stalkMap z).hom (sval s₂ (pullback.snd T.β C.α) (g z) J₀) := by
    have e₁ : J ((g ≫ pullback.snd T.β C.α) ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) := by
      rw [e₀ (), Category.assoc, Category.assoc, pullback.condition]
    rw [sval_of s₂ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => e₁),
      sval_of s₂ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => eJ)]
    refine gs_comp_stalk g _ z _ ?_ _
    exact Set.mem_iInter.2 fun _ => by rw [← eJ]; exact hJ₀ (pullback.snd T.β C.α ≫ C.α)
  have hz : sval s₁ (pullback.fst T.β C.α) (g z) J₀ = sval s₂ (pullback.snd T.β C.α) (g z) J₀ := by
    have h0 : cst (pullback.fst T.β C.α ≫ T.G.hom) (g z) b *
        (sval s₁ (pullback.fst T.β C.α) (g z) J₀ - sval s₂ (pullback.snd T.β C.α) (g z) J₀) = 0 := by
      rw [mul_sub, key, sub_self]
    have := GlobalTheory.cst_dvd_of_cst_mul_eq_zero (pullback.fst T.β C.α ≫ T.G.hom) (g z) (a := b) (b := 0)
      (fun c hc => zero_dvd_iff.2 ((mul_eq_zero.1 hc).resolve_left hb)) h0
    rw [cst_zero', zero_dvd_iff, sub_eq_zero] at this
    exact this
  rw [A₁, A₂, hz]

end GlobalTheory.Mum.Rescale

namespace GlobalTheory.Mum.Rescale

theorem cst_unit {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) {u : V} (hu : IsUnit u) :
    IsUnit (cst q z u) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨cst q z w, cst q z ↑w⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.mul_inv, ReciprocityTheory.ChartRestriction.G.H1.cst_one]
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.inv_mul, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

theorem rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  intro R _ _ _ _ D C F₁ θ₀ r t x hr hx W _ _ _ T a b v ha hb hE hbt
  obtain ⟨σ, ⟨σ', f', hC, hP, hX⟩, hσ⟩ := hE
  have hw : PGen T.ℓ := (isGen_iff T.ℓ).1 T.ℓ_gen
  obtain ⟨s, hs⟩ := sec_upK hw C.P.L.isLB T.U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 T.G.left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) σ'
  have gen : ∀ ψ : Fin 1 → (T.G.left ⟶ C.G.left), ψ = (fun _ => T.β) →
      ∀ s : LB.Sec (LB.LinComb C.P.L.L ψ (fun _ => ((1 : ℕ) : ℤ))), ∃ s' : SecK C.P.L.L T.β 1,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, sval s' r z J = sval s r z J := by
    rintro ψ rfl s
    exact ⟨s, fun _ _ _ _ => rfl⟩
  obtain ⟨s', hs'⟩ := gen _ (funext fun _ => Category.id_comp _) s
  have hs₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
      sval s' r z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r)).val * sval σ' r z J' := by
    intro Z r z J J' hJ hJ'
    rw [hs', hs Z r z J J' hJ hJ']
    simp [pw, Fin.prod_univ_one]
  let σ₁ : SecK C.P.L.L T.β 1 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom (v : W)) s'
  have hC₁ : T.Carries (v : W) σ' σ₁ := by
    intro Z r z J J' hJ hJ'
    rw [sval_secScale _ _ _ _ hJ, hs₁ Z r z J J' hJ hJ', pow_one, _root_.mul_assoc]
  have hα : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip (_root_.GlobalTheory.Mum.Modif.flat_gp R C.toModif)
  refine ⟨σ₁, ⟨σ', f', hC₁, hP, hX⟩, fun Z p p' hpp z J hJ => ?_⟩
  rw [gs_scal, ReciprocityTheory.ChartRestriction.G.H1.cst_one, _root_.one_mul]
  refine cancel C T hα b hb σ₁ _ (fun Z p p' hpp z J hJ => ?_) Z p p' hpp z J hJ
  choose I hI using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
  have hI' : Good T.U.LG.L z I := hI
  have e1 := hC Z p z J I hJ hI'
  have e2 := hσ Z p p' hpp z J hJ
  rw [e1, gs_scal, gs_scal, pow_one] at e2
  rw [sval_secScale _ _ _ _ hJ, sval_secScale _ _ _ _ hJ, hs₁ Z p z J I hJ hI', gs_scal, gs_scal]

  have hρ : ∀ c : R, cst (p ≫ T.G.hom) z (T.φ c) = cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) c) := by
    intro c
    have hm : (p ≫ T.G.hom) ≫ spMap T.φ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by
      have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
      have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
      calc (p ≫ T.G.hom) ≫ spMap T.φ = p ≫ T.G.hom ≫ T.ξ ≫ C.π := by rw [T.ξ_π, Category.assoc]
        _ = (p ≫ T.β) ≫ C.G.hom ≫ C.π := by rw [← Category.assoc T.G.hom, ← h1]; simp only [Category.assoc]
        _ = (p' ≫ C.α) ≫ C.G.hom ≫ C.π := by rw [hpp]
        _ = p' ≫ C.A.A.hom ≫ C.gp ≫ C.π := by rw [Category.assoc, ← Category.assoc C.α, h2]; simp only [Category.assoc]
        _ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by rw [C.gp_π, Category.assoc]
    rw [← cst_comp, hm, cst_comp]
  have hrU : IsUnit (cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r)) :=
    cst_unit _ _ (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr))
  have hx' : cst (p' ≫ C.A.A.hom) z x * cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r) =
      cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) t) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hx]
  have hbt' : cst (p ≫ T.G.hom) z b * cst (p ≫ T.G.hom) z (T.φ t) =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (T.φ r) * cst (p ≫ T.G.hom) z (v : W) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hbt]
  rw [hρ, hρ, ← hx'] at hbt'
  have hsc : cst (p ≫ T.G.hom) z b * cst (p' ≫ C.A.A.hom) z x =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (v : W) := by
    apply hrU.mul_right_cancel
    linear_combination hbt'
  linear_combination (cst (p ≫ T.G.hom) z (v : W)) * e2 - sval θ₀ p' z J * hsc

end GlobalTheory.Mum.Rescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarsRescale
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitRescale

variable {X Z : Scheme.{0}}

noncomputable def gsTop (f : Z ⟶ X) (z : Z) : Γ(X, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (f ⁻¹ᵁ ⊤) z trivial).hom.comp (f.app ⊤).hom

theorem gs_top (f : Z ⟶ X) (z : Z) (a : Γ(X, ⊤)) : gs f z ⊤ a = gsTop f z a := gs_eq f z ⊤ trivial a

theorem scal_comp {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ spMap φ) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) (x y : A) :
    scal q (x * y) = scal q x * scal q y := by simp only [scal, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) : scal q 1 = 1 := by
  simp only [scal, map_one]

theorem gs_top_mul (f : Z ⟶ X) (z : Z) (a b : Γ(X, ⊤)) : gs f z ⊤ (a * b) = gs f z ⊤ a * gs f z ⊤ b :=
  gs_mul f z ⊤ trivial a b

theorem gs_top_one (f : Z ⟶ X) (z : Z) : gs f z ⊤ 1 = 1 := by rw [gs_top, map_one]

theorem gs_scal {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem gs_scal_compat {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  rw [scal_comp, scal_comp, gs_scal, gs_scal]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem sval_smul {Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [show (a • s).f (fun k => J (r ≫ φ k)) = resG Y le_top a * s.f (fun k => J (r ≫ φ k)) from
    GlobalTheory.LB.smul_f a s _]
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

end GlobalTheory.Mum.TraitRescale


open GlobalTheory.Mum.TraitRescale in
theorem GlobalTheory.Mum.Trait.exp_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b : W) (u : Wˣ) (c₁ c₂ : R), a ≠ 0 → c₂ ≠ 0 → T.φ c₂ * (u : W) * a = T.φ c₁ * b → T.Exp a b s F → T.Exp 1 u (scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • s) F := by
  intro R _ _ _ hB D C W _ _ _ T k s F a b u c₁ c₂ ha hc₂ hrel hExp
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hagree⟩ := hExp
  obtain ⟨σ'', hcar''⟩ := _root_.GlobalTheory.Mum.Trait.exists_carries R D C W T k (u : W) σ'
  refine ⟨σ'', ⟨σ', f', hcar'', hpull, hexp⟩, ?_⟩
  have hφ2 : T.φ c₂ ≠ 0 := fun h0 => hc₂ (T.inj (h0.trans (map_zero T.φ).symm))
  have hb : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hrel
    exact (mul_ne_zero (mul_ne_zero hφ2 u.ne_zero) ha) hrel
  set c : FractionRing R := algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂ with hc
  have hc₂K : algebraMap R (FractionRing R) c₂ ≠ 0 :=
    fun h0 => hc₂ (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  have hcc : c * algebraMap R (FractionRing R) c₂ = algebraMap R (FractionRing R) c₁ := div_mul_cancel₀ _ hc₂K
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ'' p z J =
        gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J) := by
    intro Z p p' h z J hJ
    choose J' hJ' using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
    have e1 := hcar Z p z J J' hJ hJ'
    have e2 := hcar'' Z p z J J' hJ hJ'
    have e3 := hagree Z p p' h z J hJ

    have m : gs p z ⊤ (scal T.G.hom (T.φ c₂)) * gs p z ⊤ (scal T.G.hom (u : W)) * gs p z ⊤ (scal T.G.hom a) =
        gs p z ⊤ (scal T.G.hom (T.φ c₁)) * gs p z ⊤ (scal T.G.hom b) := by
      have := congrArg (fun w => gs p z ⊤ (scal T.G.hom w)) hrel
      simpa only [scal_mul, gs_top_mul] using this
    rw [gs_scal_compat T p p' h z c₁, gs_scal_compat T p p' h z c₂] at m
    have hC : gs p' z ⊤ (scal C.A.A.hom c) * gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) =
        gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₁)) := by
      rw [← hcc, scal_mul, gs_top_mul]
    have hU : IsUnit (gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) := by
      obtain ⟨v, hv⟩ := Ne.isUnit hc₂K
      have : IsUnit (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) :=
        IsUnit.of_mul_eq_one (scal C.A.A.hom ((v⁻¹ : (FractionRing R)ˣ) : FractionRing R))
          (by rw [← scal_mul, ← hv, Units.mul_inv, scal_one])
      rw [gs_top]
      exact this.map _
    have e13 := e1.symm.trans e3
    rw [e2]
    apply hU.mul_right_cancel
    linear_combination (gs p z ⊤ (scal T.G.hom (u : W)) *
      gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) * e13 + sval s p' z J * m -
      (gs p z ⊤ (scal T.G.hom b) * sval s p' z J) * hC
  intro Z p p' h z J hJ
  rw [scal_one, gs_top_one, _root_.one_mul, sval_smul C.P.L.L _ s p' z hJ]
  by_cases hF : IsField R
  · exact _root_.GlobalTheory.Mum.cancel_field R hB D C W T k σ'' s b c hF hb key Z p p' h z J hJ
  · exact (_root_.GlobalTheory.Mum.unit_nonfield R D C W T Z p p' h hF b hb z).mul_left_cancel (key Z p p' h z J hJ)

end
end

