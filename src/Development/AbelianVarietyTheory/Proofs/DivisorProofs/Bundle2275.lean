module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransport

variable {S' Z : Scheme.{0}} {π : S' ⟶ Z} {M : LB Z} {L : LB S'} {N : ℕ}

theorem w_trans (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ S') (y : Y)
    (i i' : L.ι) (k k' : M.ι) (hi : f y ∈ L.U i) (hi' : f y ∈ L.U i') (hk : (f ≫ π) y ∈ M.U k)
    (hk' : (f ≫ π) y ∈ M.U k') :
    gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y (L.U i ⊓ L.U i') (L.g i i') ^ (N : ℤ) * (gm (f ≫ π) y (M.U k ⊓ M.U k') (M.g k k'))⁻¹ *
        gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) := by
  have m1 : f y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have m1' : f y ∈ (lbPow L N).U (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have m2 : f y ∈ (M.pull π).U (fun _ => k) := Set.mem_iInter.2 fun _ => hk
  have m2' : f y ∈ (M.pull π).U (fun _ => k') := Set.mem_iInter.2 fun _ => hk'
  have hm : f y ∈ (lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) := ⟨⟨m1, m2⟩, ⟨m1', m2'⟩⟩
  have e := congrArg (gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')))) (hw (fun _ => i, fun _ => k) (fun _ => i', fun _ => k'))
  have e1 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_left (w.s (fun _ => i, fun _ => k))) :=
    (gm_res f y _ hm _).symm
  have e2 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_right (w.s (fun _ => i', fun _ => k'))) =
      gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) :=
    gm_res f y _ hm _
  have e3 := gm_div (M.pull π) (lbPow L N) f y (fun _ => i, fun _ => k) (fun _ => i', fun _ => k') hm
  refine e1.trans (e.trans ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·) (e3.trans ?_) e2)))
  exact congrArg₂ (fun a b => a * b⁻¹)
    ((gm_linComb L (fun _ => 𝟙 S') (fun _ => (N : ℤ)) f y (fun _ => i) (fun _ => i') m1 m1').trans
      (by rw [Fintype.prod_unique, Category.comp_id]))
    (gm_pull_g M π f y (fun _ => k) (fun _ => k') m2 m2')

theorem alg₁ {G : Type*} [CommGroup G] (t E W : G) (N : ℕ) :
    (t * E) ^ N * (t ^ (N : ℤ) * 1⁻¹ * W)⁻¹ = E ^ N * W⁻¹ := by
  rw [zpow_natCast, inv_one, _root_.mul_one, _root_.mul_pow, _root_.mul_inv, _root_.mul_comm (t ^ N),
    _root_.mul_assoc, mul_inv_cancel_left]

theorem alg₂ {G : Type*} [CommGroup G] (E g W : G) (N : ℕ) :
    E ^ N * ((1 : G) ^ (N : ℤ) * g⁻¹ * W)⁻¹ = g * (E ^ N * W⁻¹) := by
  rw [one_zpow, _root_.one_mul, _root_.mul_inv, inv_inv, _root_.mul_left_comm]

theorem exists_strictHenselian_absolutely_closed_local_ring (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen)
    {A : Scheme.{0}} (a : A ⟶ S') (e : LB.Gen (L.pull a)) (he : e.IsGen) :
    ∃ t : LB.Gen (M.pull (a ≫ π)), t.IsGen ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι) (k : M.ι),
      (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z ((M.pull (a ≫ π)).U (fun _ => k)) (t.s (fun _ => k)) =
        gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
  have loc : ∀ k : M.ι, ∃ s : Γ(A, (M.pull (a ≫ π)).U (fun _ => k))ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y)
      (i : L.ι), (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z _ s = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
    intro k
    let V := (M.pull (a ≫ π)).U (fun _ => k)
    let W : L.ι → A.Opens := fun i => V ⊓ (L.pull a).U (fun _ => i)
    have h1 : ∀ i, W i ≤ (L.pull a).U (fun _ => i) := fun i => inf_le_right
    have h2 : ∀ i, W i ≤ a ⁻¹ᵁ ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) := fun i x hx =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.2 (), Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 ()⟩
    let u : ∀ i, Γ(A, W i)ˣ := fun i =>
      res (h1 i) (e.s (fun _ => i)) ^ N * (res (h2 i) (pullU a _ (w.s (fun _ => i, fun _ => k))))⁻¹
    have hu : ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι), r z ∈ W i →
        gm r z (W i) (u i) = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
      intro Y r z i hz
      simp only [u, map_mul, map_pow, map_inv]
      exact congrArg₂ (fun p q => p ^ N * q⁻¹) (gm_res r z (h1 i) hz _)
        ((gm_res r z (h2 i) hz _).trans (gm_pull r a z _ (h2 i hz) _))
    obtain ⟨s, hs⟩ := glue_unit V W (fun i => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL (a x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩) u
      (fun i j x hx => by
        have hi : (𝟙 A ≫ a) x ∈ L.U i := Set.mem_iInter.1 hx.1.2 ()
        have hj : (𝟙 A ≫ a) x ∈ L.U j := Set.mem_iInter.1 hx.2.2 ()
        have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U k := Set.mem_iInter.1 hx.1.1 ()
        have g1 : gm (𝟙 A) x ((L.pull a).U fun _ => i) (e.s fun _ => i) =
            trF (fun _ : PUnit => a) (fun _ => 1) (𝟙 A) x (fun _ => i) (fun _ => j) *
              gm (𝟙 A) x ((L.pull a).U fun _ => j) (e.s fun _ => j) := gen_trans he (𝟙 A) x hx.1.2 hx.2.2
        rw [hu A (𝟙 A) x i hx.1, hu A (𝟙 A) x j hx.2, g1,
          w_trans w hw (𝟙 A ≫ a) x i j k k hi hj hk hk, gm_self hM _ x hk]
        simp only [trF, Fintype.prod_unique, zpow_one]
        exact alg₁ _ _ _ N)
    refine ⟨s, fun Y r z i hi hk => ?_⟩
    have hz : r z ∈ W i := ⟨Set.mem_iInter.2 fun _ => hk, Set.mem_iInter.2 fun _ => hi⟩
    rw [← gm_res r z (inf_le_left : W i ≤ V) hz, hs i, hu Y r z i hz]
  choose s hs using loc
  refine ⟨⟨fun k => s (k ())⟩, fun k k' => unit_ext fun x hx => ?_, fun Y r z i k hi hk => hs k Y r z i hi hk⟩
  refine (gm_res (𝟙 A) x _ hx _).trans (Eq.trans ?_ ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_pull_g M (a ≫ π) (𝟙 A) x k k' hx.1 hx.2) (gm_res (𝟙 A) x _ hx _))).symm)
  obtain ⟨i, hi⟩ := exists_chart hL ((𝟙 A ≫ a) x)
  have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k ()) := Set.mem_iInter.1 hx.1 ()
  have hk' : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k' ()) := Set.mem_iInter.1 hx.2 ()
  have v1 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k) (s (k ())) = _ := hs (k ()) A (𝟙 A) x i hi hk
  have v2 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k') (s (k' ())) = _ := hs (k' ()) A (𝟙 A) x i hi hk'
  rw [v1, v2, w_trans w hw (𝟙 A ≫ a) x i i (k ()) (k' ()) hi hi hk hk', gm_self hL (𝟙 A ≫ a) x hi, Category.assoc]
  exact alg₂ _ _ _ N

theorem transport : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  intro S' Z π M L N hM hL hw0
  obtain ⟨w, hw⟩ := hw0
  classical
  refine ⟨fun A a e => if he : e.IsGen then (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose else ⟨fun _ => 1⟩,
    fun A a e he => ?_, ?_⟩
  · simp only [dite_eq_left he]
    exact (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.1
  · intro A A' Y a a' e e' r r' he he' hr hval z J hJ
    simp only [dite_eq_left he, dite_eq_left he']
    have hk : (r ≫ a ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hJ _
    have hk'e : J (r' ≫ a' ≫ π) = J (r ≫ a ≫ π) := by rw [← Category.assoc, ← hr, Category.assoc]
    have hk' : (r' ≫ a' ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hk'e ▸ hJ _
    obtain ⟨i, hi⟩ := exists_chart hL ((r ≫ a) z)
    have hi' : (r' ≫ a') z ∈ L.U i := by rw [← hr]; exact hi
    obtain ⟨JL, hJL, eJL⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ a) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hi)
    have v1 := val_of (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z JL (fun _ => i) (fun _ => eJL ())
    have v2 := val_of (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z JL (fun _ => i)
      (fun _ => by rw [← hr]; exact eJL ())
    have hv := hval z JL hJL
    rw [v1, v2] at hv
    rw [val_of (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) _ r z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => rfl),
      val_of (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) _ r' z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => hk'e)]
    refine (((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.2 Y r z i _ hi hk).trans ?_).trans
      ((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a' e' he').choose_spec.2 Y r' z i _ hi' hk').symm
    rw [hr]
    congr 1
    exact congrArg (· ^ N) hv

end GlobalTheory.GenTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTupleThetaConstantRatiosGenerateField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem thetaSys_gen_tuple (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) :
    ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧
      Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun i => match i with | none => 1 | some y => (y : Ω)
  refine ⟨Option s, inferInstance, t₀, ⟨none, one_ne_zero⟩, ?_⟩
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hK
  have hbase : ∀ a : o, algebraMap o Ω a ∈ K := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hgen : ∀ y ∈ s, y ∈ K := by
    intro y hy
    apply Subfield.subset_closure
    refine Or.inr ⟨(x₀, none), (x₀, some ⟨y, hy⟩), ?_⟩
    simp only [t₀, mul_one]
    field_simp
  let KA : Subalgebra o Ω :=
    { K.toSubring with algebraMap_mem' := hbase }
  have hR : S.R ≤ KA := by
    rw [← hs]
    exact Algebra.adjoin_le (fun y hy => hgen y hy)
  have hall : ∀ x : Ω, x ∈ K := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact K.div_mem (hR ha) (hR hb)
  refine ⟨⟨{1}, eq_top_iff.mpr fun x _ => ?_⟩⟩
  simp only [Finset.coe_singleton]
  rw [Submodule.mem_span_singleton]
  exact ⟨⟨x, hall x⟩, by simp [Algebra.smul_def]; rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SymPrincipalTranslate
open GlobalTheory.CechPic

theorem pull_local_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (c : Pic X) :
    pull f c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hc : f.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  exact GlobalTheory.KTrivOfLam.pull_eq_zero_of_chart hL f i fun y =>
    ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open (L.U i).isOpen hi

theorem cls_lam_div {S : Scheme.{0}} {G : Over S} [GrpObj G] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : (abelian₂ G (LB.div L M)).IsLB) (h₁ : (abelian₂ G L).IsLB) (h₂ : (abelian₂ G M).IsLB) :
    cls _ h = cls _ h₁ - cls _ h₂ := by
  rw [show cls (abelian₂ G (LB.div L M)) h = _ from cls_linComb (LB.isLB_div hL hM) _ _ h,
    show cls (abelian₂ G L) h₁ = _ from cls_linComb hL _ _ h₁, show cls (abelian₂ G M) h₂ = _ from cls_linComb hM _ _ h₂,
    cls_div hL hM, ← Finset.sum_sub_distrib]
  simp only [map_sub, smul_sub]

theorem exists_two_torsion_rigTransl : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  intro R _ _ _ P L' hL' _ hsym hlam
  have := P.isAb.comm
  have hO : (LB.div L' P.L).IsLB := LB.isLB_div hL' P.isLB
  have hΛ' : (abelian₂ P.A L').IsLB := LB.isLB_linComb hL' _ _
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hΛO : (abelian₂ P.A (LB.div L' P.L)).IsLB := LB.isLB_linComb hO _ _
  have hu : ∃ u : LB.Gen (abelian₂ P.A (LB.div L' P.L)), u.IsGen := by
    refine (cls_eq_zero_iff hΛO).1 ?_
    rw [cls_lam_div hL' P.isLB hΛO hΛ' hΛ, sub_eq_zero]
    exact (cls_eq_iff hΛ' hΛ).2 hlam
  obtain ⟨x, hx⟩ := GlobalTheory.LN.ega_holds.2.2.2 R P _ hO hu
  let τ : P.A ⟶ P.A := (toUnit P.A ≫ x) * 𝟙 P.A

  have hτ : cls L' hL' = pull τ.left (cls P.L P.isLB) := by
    have h1 := (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hx
    rw [cls_div hL' P.isLB hO, cls_linComb P.isLB] at h1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul, pull_id] at h1
    exact sub_left_injective (h1.trans (sub_eq_add_neg _ _).symm)

  have hR : (GlobalTheory.RigidTranslate.rigTransl P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have hcR : cls _ hR = pull τ.left (cls P.L P.isLB) := by
    have e : GlobalTheory.PolTranslate.transl x = τ := by rw [GlobalTheory.PolTranslate.transl, _root_.mul_comm]
    refine (cls_linComb P.isLB _ _ hR).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    rw [Over.comp_left, pull_comp, pull_local_eq_zero (R := R) x.left, map_zero, neg_zero, add_zero, e]
  refine ⟨x, ?_, (cls_eq_iff hL' hR).1 (hτ.trans hcR.symm)⟩

  have hs : pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB :=
    GlobalTheory.RigSymSubring.cls_of_sym P.isLB P.sym
  have hs' : pull (GrpObj.inv : P.A ⟶ P.A).left (cls L' hL') = cls L' hL' :=
    GlobalTheory.RigSymSubring.cls_of_sym hL' hsym
  let τ' : P.A ⟶ P.A := (toUnit P.A ≫ x⁻¹) * 𝟙 P.A
  have e1 : (GrpObj.inv : P.A ⟶ P.A) ≫ τ = τ' ≫ GrpObj.inv := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv,
      ← GrpObj.comp_inv, inv_inv, Hom.inv_def, Category.id_comp]
  have e2 : τ ≫ τ' = 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.one_mul]
  have e3 : τ ≫ τ = (toUnit P.A ≫ (x * x)) * 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul]
  have h2 : pull ((toUnit P.A ≫ (x * x)) * 𝟙 P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
    have k : pull τ'.left (cls P.L P.isLB) = pull τ.left (cls P.L P.isLB) := by
      have := hs'
      rw [hτ, ← pull_comp, ← Over.comp_left, e1, Over.comp_left, pull_comp, hs] at this
      exact this
    have k2 := congrArg (pull τ.left) k
    rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, e2, e3, Over.id_left, pull_id] at k2
    exact k2.symm

  refine (P.ktriv R (𝟙 (Sp R)) (x * x) fun p => ⟨⊤, trivial, ?_⟩).trans Hom.one_def.symm
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  have hTD : (translDiff P.A P.L (x * x)).IsLB := LB.isLB_linComb P.isLB _ _
  refine (cls_eq_zero_iff (pull_isLB hTD _)).1 ?_
  rw [cls_pull hTD]
  suffices h0 : cls _ hTD = 0 by rw [h0, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A]).left (cls P.L P.isLB) -
      pull (snd T P.A).left (cls P.L P.isLB) := by
    refine (cls_linComb P.isLB _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A] = snd T P.A ≫ ((toUnit P.A ≫ (x * x)) * 𝟙 P.A) := by
    show (fst T P.A ≫ (x * x)) * snd T P.A = _
    rw [MonObj.comp_mul (snd T P.A), ← Category.assoc (snd T P.A), comp_toUnit, Category.comp_id]
    congr 1
  rw [e₁, e₂, Over.comp_left, pull_comp, h2, sub_self]
end GlobalTheory.SymPrincipalTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorusLift

open GlobalTheory.UU GlobalTheory.FormalPoint

section Lift

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem exists_coords (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (e : ℕ) :
    ∃ y : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
      RedOnto.Coords U e g (thick R I e) y :=
  RedOnto.exists_coords U e g (thick R I e) (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)

variable [IsLocalRing R]


variable {U} in
theorem red_unique [IsHausdorff I R] {g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  choose y hy using exists_coords U g
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)
  exact (RedOnto.comp_fstG_eq h (hy e)).symm.trans (RedOnto.comp_fstG_eq h' (hy e))

theorem exists_red [IsAdicComplete I R] (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G, U.Red x g := by
  choose y hy using exists_coords U g
  have hf : IsAdicFamily I fun e => y e ≫ (fstG I e G).left := fun e => by
    have h₁ := (hy (e + 1)).comp (adicLevelMap I (Nat.le_succ (e + 1)))
    have h₂ : adicLevelMap I (Nat.le_succ (e + 1)) ≫ thick R I (e + 1) = thick R I e := adicLevelMap_ι _ _
    have h₃ : RedOnto.Coords U (e + 1) g (thick R I e) (adicLevelMap I (Nat.le_succ (e + 1)) ≫ y (e + 1)) :=
      h₂ ▸ h₁
    have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left)
      (h₃.unique (hy e).succ)).trans ((Category.assoc _ _ _).trans (congrArg _ h₄)))
  obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) G.hom hf fun e => by
    have h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))
  refine ⟨Over.homMk x hx₁, fun e Z r xe hxe => ?_⟩
  have hr : r = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    have := congrArg (· ≫ G.hom) hxe
    simp only [Category.assoc, Over.homMk_left, hx₁] at this
    rw [← Category.comp_id r]
    refine this.symm.trans ?_
    rw [Over.w (fstG I e G)]
    rfl
  have hxe' : xe = (xe ≫ (thickObj R I e G).hom) ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, ← hx₂ e, hxe]
    simp only [Over.homMk_left]
    rw [hr, Category.assoc]
  have := (hy e).comp (xe ≫ (thickObj R I e G).hom)
  rw [← hr, ← hxe'] at this
  exact this

end Lift

theorem exists_sec_sq_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  intro R _ _ _ hR D A G _ _ hS U g hg
  obtain ⟨z, hz, hgz⟩ := hg
  have : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre GlobalTheory.globalFns_holds hS w hw
  obtain ⟨a, ha⟩ := exists_red U' g
  refine ⟨a, ?_, fun e ae _ hae => ?_⟩
  · rw [pow_two]
    exact red_unique (RedAdd.red_mul GlobalTheory.globalFns_holds ha ha hgz) (RedAdd.red_one U' hz)
  · obtain ⟨h₁, h₂⟩ := ha e _ (thick R (maximalIdeal R) e) ae hae
    refine ⟨h₁, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
    rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact h₂ χ y J hJ

end GlobalTheory.TorusLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DVRExt

theorem exists_unique_extend : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  intro R _ P W L _ _ _ _ _ _ f x
  haveI : ValuationRing W := inferInstance
  have hv : ValuativeCriterion P.A.hom := by
    have h : IsProper P.A.hom := P.isAb.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x.left ≫ P.A.hom = spMap (algebraMap W L) ≫ spMap f := by
    rw [Over.w x]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let S : ValuativeCommSq P.A.hom :=
    { R := W, K := L, i₁ := x.left, i₂ := spMap f, commSq := ⟨hsq⟩ }
  have hU := (hv S).some
  refine ⟨Over.homMk hU.default.l hU.default.fac_right, hU.default.fac_left, ?_⟩
  intro y hy
  have hy2 : y.left ≫ P.A.hom = spMap f := Over.w y
  let T : S.commSq.LiftStruct := ⟨y.left, hy, hy2⟩
  have hT : T = hU.default := hU.uniq T
  apply Over.OverMorphism.ext
  change T.l = hU.default.l
  rw [hT]

end GlobalTheory.DVRExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentElem
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_elem : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (a : D'), a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a →
      ∃ e : D, algebraMap D D' e = a := by
  intro D D' _ _ _ _ a h
  have hx : FlatDescent.amitsurDiff (A := D) D' D (a ⊗ₜ[D] (1 : D)) = 0 := by
    apply (LinearEquiv.lTensor D' (TensorProduct.rid D D')).injective
    simp [FlatDescent.amitsurDiff_tmul, h]
  obtain ⟨m, hm⟩ := ((FlatDescent.amitsur_exact (A := D) (B := D') (M := D)).2 _).1 hx
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.rid D D') hm
  simpa [Algebra.algebraMap_eq_smul_one] using this

end GlobalTheory
end

