module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.HTPair

namespace GlobalTheory.QuotField

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

def levelRes (m : ℕ) : G.A (m + 1) →ₐc[O] G.A 1 :=
  Nat.rec (motive := fun m => G.A (m + 1) →ₐc[O] G.A 1) (BialgHom.id O _)
    (fun m f => f.comp (G.res (m + 1))) m

theorem levelRes_surjective (m : ℕ) : Function.Surjective (levelRes G m) := by
  induction m with
  | zero => exact Function.surjective_id
  | succ m ih =>
    intro c
    obtain ⟨a, rfl⟩ := ih c
    obtain ⟨b, rfl⟩ := G.res_surjective (m + 1) a
    exact ⟨b, rfl⟩

theorem ker_succ {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    RingHom.ker (π.comp (levelRes G (m + 1))) =
      Ideal.comap (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1))
        (RingHom.ker (π.comp (levelRes G m))) :=
  Ideal.ext fun _ => Iff.rfl

theorem torsion_le {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    torsionIdeal (R := O) (A := G.A (m + 1)) p ≤ RingHom.ker (π.comp (levelRes G m)) := by
  refine (kerIdeal_le_ker_iff _
    ((π.comp (levelRes G m) : G.A (m + 1) →ₐc[O] C) : G.A (m + 1) →ₐ[O] C)).2 fun c => ?_
  change π (levelRes G m (mulBy (R := O) (A := G.A (m + 1)) p c)) = _
  have h := G.mulBy_pow_self 1 (levelRes G m c)
  rw [pow_one] at h
  rw [map_mulBy, h, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

end GlobalTheory.QuotField


open GlobalTheory.QuotField GlobalTheory.HTPair.QuotIsog in
theorem GlobalTheory.HTPair.exists_quot_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G : PDivGroup p k) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π →
    ∃ (Q : PDivGroup p k) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) • 𝟙 G ∧
      q' ≫ q = (p : ℤ_[p]) • 𝟙 Q ∧ kerIdeal (q.app 1) = RingHom.ker π := by
  intro p _ k _ _ G C _ _ _ _ π hπ
  have hsurj : ∀ m, Function.Surjective (π.comp (levelRes G m)) := fun m =>
    hπ.comp (levelRes_surjective G m)
  choose B iR iH iC iF j hinj hker huniv using
    fun m => _root_.GlobalTheory.HopfQuot.exists_quotient k (G.A (m + 1)) C (π.comp (levelRes G m)) (hsurj m)
  letI := iR
  letI := iH
  letI := iC
  letI := iF
  have hρ : ∀ m, ∃ ρ : G.A (m + 1) →ₗ[k] B m, ∀ b, ρ (j m b) = b := fun m => by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      ((j m : B m →ₐ[k] G.A (m + 1)).toLinearMap) (LinearMap.ker_eq_bot.2 (hinj m))
    exact ⟨g, fun b => LinearMap.congr_fun hg b⟩
  choose ρ hρ using hρ
  have hfac : ∀ m (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] G.A (m + 1)),
      kerIdeal f ≤ RingHom.ker (π.comp (levelRes G m)) →
        ∃ g : D →ₐc[k] B m, ∀ d, j m (g d) = f d := fun m D _ _ f hf =>
    _root_.GlobalTheory.bialgHom_factor_through_split k (G.A (m + 1)) (B m) D (j m) (ρ m) f (hρ m) (huniv m D f hf)
  choose r hr using fun m => hfac m (B (m + 1)) ((G.res (m + 1)).comp (j (m + 1))) (by
    rw [kerIdeal_comp, hker (m + 1), ker_succ]
    exact Ideal.map_comap_le)
  choose s hs using fun m => hfac m (G.A m) (G.mulP m) (by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]
    exact torsion_le G π m)
  have hkr : ∀ m, kerIdeal (j m) =
      Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1)) (kerIdeal (j (m + 1))) := by
    intro m
    rw [hker, hker, ker_succ]
    exact (Ideal.map_comap_of_surjective (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1))
      (G.res_surjective (m + 1)) _).symm
  let τ : QuotTower G :=
    { B := B
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := iF
      projective := fun _ => inferInstance
      j := j
      ρ := ρ
      r := r
      s := s
      ρ_j := hρ
      r_surjective := fun m => _root_.GlobalTheory.QuotTransition.transition_surjective k (G.A (m + 1)) (G.A (m + 2)) (B m) (B (m + 1))
        (G.res (m + 1)) (j m) (j (m + 1)) (r m) (ρ m) (hρ m) (fun b => hr m b) (hkr m)
      j_r := fun m b => hr m b
      j_s := hs
      tors_le := fun m => (hker m).symm ▸ torsion_le G π m }
  obtain ⟨H, q, hqs, hqk, hqc⟩ := GlobalTheory.HTPair.exists_quotPDivGroup p k G τ
  refine ⟨H, toQuot τ q hqs hqk hqc, fromQuot τ q hqc, ?_, ?_, ?_⟩
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun a => ?_
    change (toQuot τ q hqs hqk hqc).app n (q n (τ.s n a)) = _
    rw [toQuot_app_q, τ.j_s, G.res_mulP]
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun c => ?_
    obtain ⟨b, rfl⟩ := hqs n c
    change q n (τ.s n ((toQuot τ q hqs hqk hqc).app n (q n b))) = _
    rw [toQuot_app_q, s_res_j, map_mulBy]
  · have h1 : ((toQuot τ q hqs hqk hqc).app 1).comp (q 1) = (G.res 1).comp (τ.j 1) :=
      BialgHom.ext fun b => toQuot_app_q τ q hqs hqk hqc 1 b
    rw [← kerIdeal_comp_of_surjective _ (hqs 1), h1, kerIdeal_comp]
    exact (τ.map_res_kerIdeal 0).trans ((hker 0).trans (Ideal.ext fun _ => Iff.rfl))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatio
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.HTQuot

theorem objMap_comp_φ_of_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem obj_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (G : Type)
    [Group G] (ρ : G → (X ⟶ X)) (o : Obj b N (π ≫ sY)), GlobalTheory.ZM.IsGaloisCover G ρ π → IsQProjOver (π ≫ sY) →
    IsQProjOver sY → (∀ a, Nonempty (ObjMap o o (ρ a))) → ∃ oY : Obj b N sY, Nonempty (ObjMap o oY π) := by
  intro p _ D R _ _ b N hN hNp X Y π sY G _ ρ o hG hq hqY hmaps
  have : IsLocallyNoetherian Y := by
    obtain ⟨M, i, hi, -, hi'⟩ := hqY
    have := isProper_str R M
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str R M)
  have m : ∀ a, ObjMap o o (ρ a) := fun a => (hmaps a).some
  let ν : G → (o.A.left ⟶ o.A.left) := fun a => (m a).φ
  have uniq : ∀ {f f' : X ⟶ X} (_ : f = f') (m₁ : ObjMap o o f) (m₂ : ObjMap o o f'), m₁.φ = m₂.φ := by
    rintro f f' rfl m₁ m₂
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp X X _ _ o o f m₁ m₂
  have ν1 : ν 1 = 𝟙 _ := by
    have key : ∀ {f : X ⟶ X} (_ : f = 𝟙 X) (m₁ : ObjMap o o f), m₁.φ = 𝟙 _ := by
      rintro f rfl m₁
      exact GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp X _ o m₁
    exact key hG.one (m 1)
  have νmul : ∀ a c, ν (a * c) = ν a ≫ ν c := by
    intro a c
    obtain ⟨m', hm'⟩ := objMap_comp_φ_of_comp (m a) (m c)
    exact (uniq (hG.mul a c) (m (a * c)) m').trans hm'
  have hcart : ∀ a, IsGrpPullback o.A o.A (ρ a) (ν a) := fun a => (m a).cart
  have hqA : IsQProjOver (o.A.hom ≫ π ≫ sY) :=
    GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth R X (π ≫ sY) o.A _ hq (pull_isLB o.isLB _) o.ample
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ :=
    GlobalTheory.abelianScheme_descends_galoisCover_noetherian R X Y π sY G ρ o.A ν hG hqA o.ab hcart ν1 νmul
  have := hA₀.comm
  obtain ⟨act₀, hact⟩ := GlobalTheory.GaloisActDesc.exists_oActN_descend D.O X Y π G ρ o.A A₀ φ ν o.act hG o.ab hA₀ gp hφ
    hcart (fun a c => (m a).act c)
  obtain ⟨P₀, φ₂, hP₀, hsq, iso, rig0⟩ := GlobalTheory.SquareDescent.exists_bundle_descent X Y π G ρ o.A A₀ φ ν o.P hG o.ab
    hA₀ gp hφ hcart ν1 νmul o.isLB o.rig₁ (fun a => ⟨(m a).φ₂, (m a).sq, (m a).pol⟩)
  obtain ⟨rig₁, rig₂⟩ := _root_.GlobalTheory.DescGalRig.exists_gen_lift_of_descent X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.rig₁ o.rig₂
  have symm := _root_.GlobalTheory.DescSymm.lbIso_swap X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.symm
  have ample := _root_.GlobalTheory.DescGal.relAmple_diag_descends X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso o.ample
  have kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ A₀),
      (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.descended_polarisation_kernel_killed_same_integer X Y π G ρ o.A A₀ φ φ₂ o.P P₀ e hG o.ab hA₀ gp hsq o.isLB hP₀ iso hk⟩
  have rosati := _root_.GlobalTheory.RosatiDescent.lbIso_act_descent D.O (fun c => (D.star c).unop) X Y π G ρ o.A A₀ φ φ₂ o.P P₀ o.act act₀ hG o.ab hA₀ gp
    hsq o.isLB hP₀ iso rig0 hact o.rosati
  obtain ⟨eta₀, eta_add, eta_lin, eta_ker, heta⟩ := GlobalTheory.LevelSecDesc.levelSections_descend D.O D.La N X Y π G ρ o.A A₀ φ
    ν o.act act₀ o.eta hG gp hφ hact (fun a y => (m a).eta y) o.eta_add o.eta_lin o.eta_ker
  have lie := GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lie
  have lieRank := _root_.GlobalTheory.LieDesc.lieMult_descend p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lieRank
  have geom := _root_.GlobalTheory.UPel.HT.geom_descends_galoisCover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ N φ₂ o.P P₀ o.eta eta₀ hG o.ab hA₀ gp hact hsq
    o.isLB hP₀ iso heta o.geom
  let oY : Obj b N sY :=
    { A := A₀, ab := hA₀, act := act₀, P := P₀, isLB := hP₀, rig₁ := rig₁, rig₂ := rig₂, symm := symm
      ample := ample, kerP := kerP, rosati := rosati, lie := lie, lieRank := lieRank, eta := eta₀,
      eta_add := eta_add, eta_lin := eta_lin, eta_ker := eta_ker, geom := geom }
  exact ⟨oY, ⟨⟨φ, φ₂, gp, hsq, hact, iso, heta⟩⟩⟩

theorem exists_repFam_of_levelCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (u : Obj b N s) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)),
    IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) →
    (∀ a, Nonempty (ObjMap u u (ρ a))) →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) →
    (∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : Ga → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧ y ≫ s = π₁ ≫ t ∧
        Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : Ga), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') →
    ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp X s u Ga _ _ ρ hq h1 hmul hbase hmaps hfree hcov huniq
  obtain ⟨Y, π, sY, hπs, hgal, hsep, hlft, -⟩ :=
    GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian R X s Ga ρ hq h1 hmul hbase hfree
  have hqY : IsQProjOver sY := GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover R X Y π sY Ga ρ
    hgal hsep hlft (by rw [hπs]; exact hq)
  subst hπs
  obtain ⟨uY, ⟨mu⟩⟩ := obj_descends_galoisCover p D R b N hN hNp X Y π sY Ga ρ u hgal hq hqY hmaps
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'),
      ∃! f : S ⟶ Y, f ≫ sY = s' ∧ Nonempty (ObjMap o uY f) := by
    intro S s' o
    obtain ⟨S₁, π₁, ρ₁, y, o', hgal₁, hequi, hys, ⟨m₁⟩, ⟨m₂⟩⟩ := hcov S s' o
    have hinv : ∀ a, ρ₁ a ≫ (y ≫ π) = y ≫ π := by
      intro a; rw [← Category.assoc, hequi a, Category.assoc, hgal.inv a]
    obtain ⟨f, hf, hfu⟩ := hgal₁.existsUnique_desc (y ≫ π) hinv
    have canc : ∀ {Z : Scheme.{0}} (h₁ h₂ : S ⟶ Z), π₁ ≫ h₁ = π₁ ≫ h₂ → h₁ = h₂ := by
      intro Z h₁ h₂ e
      obtain ⟨w, -, hwu⟩ := hgal₁.existsUnique_desc (π₁ ≫ h₁) (fun a => by rw [← Category.assoc, hgal₁.inv a])
      exact (hwu h₁ rfl).trans (hwu h₂ e.symm).symm
    have hfs : f ≫ sY = s' := canc _ _ (by rw [← Category.assoc, hf, Category.assoc, hys])
    have hmf : Nonempty (ObjMap o uY f) := by
      obtain ⟨m₃⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' u uY y π m₂ mu
      rw [← hf] at m₃
      exact GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover p D R b N S S₁ Y s' sY π₁ Ga ρ₁ f o o' uY hN hNp hgal₁ m₁ m₃
    refine ⟨f, ⟨hfs, hmf⟩, ?_⟩
    rintro f' ⟨hf's, ⟨m'⟩⟩
    obtain ⟨m₄⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' o uY π₁ f' m₁ m'
    obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ (pullback (π₁ ≫ f') π) (π₁ ≫ s')
      (pullback.fst (π₁ ≫ f') π) o'
    obtain ⟨mT1⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' u _ y mT m₂
    obtain ⟨mT2⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' uY _ _ mT m₄
    rw [pullback.condition] at mT2
    obtain ⟨mT3⟩ := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ oT u uY
      (pullback.snd (π₁ ≫ f') π) π).2 ⟨mT2⟩ ⟨mu⟩
    have key : y ≫ π = π₁ ≫ f' := by
      apply GlobalTheory.ZM.IsGaloisCover.eq_of_local_eq_pullback X Y S₁ Y π Ga ρ (π₁ ≫ f') (y ≫ π) (π₁ ≫ f') hgal
      intro q
      obtain ⟨V, a, hqV, hV⟩ := huniq _ _ oT (pullback.fst (π₁ ≫ f') π ≫ y) (pullback.snd (π₁ ≫ f') π)
        (by rw [Category.assoc, hys])
        (by rw [← Category.assoc, ← pullback.condition]; simp [hf's]) ⟨mT1⟩ ⟨mT3⟩ q
      refine ⟨V, hqV, ?_⟩
      calc V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ y ≫ π
          = (V.ι ≫ (pullback.fst (π₁ ≫ f') π ≫ y) ≫ ρ a) ≫ π := by simp [hgal.inv]
        _ = (V.ι ≫ pullback.snd (π₁ ≫ f') π) ≫ π := by rw [hV]
        _ = V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ π₁ ≫ f' := by rw [Category.assoc, ← pullback.condition]
    exact hfu f' key.symm
  exact ⟨⟨Y, sY, uY, hrep⟩, hqY⟩

theorem exists_representing_family_of_level_structure : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N M e hN hNp hM hodd hMp hep hMe hperf hrep
  obtain ⟨X, s, s₁, u, lev, hlev, hq, huniv⟩ := hrep
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨ρ, h1, hmul, hact⟩ := _root_.GlobalTheory.UPel.HT.SympAct.exists_sympActs p D R b N _ M (by omega) X s s₁ u lev hlev huniv
  exact exists_repFam_of_levelCover p D R b N hN hNp X s u _ ρ hq h1 hmul (fun a => (hact a).1)
    (fun a => let ⟨m, _⟩ := (hact a).2.2; ⟨m⟩)
    (GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one p D R b N _ M hN hNp (by omega) X s s₁ u lev hlev ρ hact)
    (GlobalTheory.T.symplectic_level_over_cyclotomic p D R b N M e hN hNp hM hodd hMp hep hMe hperf X s s₁ u lev hlev huniv ρ hact)
    (GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps p D R b N _ M hN hNp hM hodd hMp X s s₁ u lev hlev huniv ρ hact)

end GlobalTheory.HTQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfAdditiveFunctionFirstLevel
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.Chart

theorem exists_series_of_cobOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 →
    ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k),
      IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  intro p _ k _ d G c μ hμ b hb
  obtain ⟨x, cc, B, -, hcob, hcounit, hB1⟩ := PDivGroup.exists_of_cobOne_eq_zero (G := G) hb
  have hfun := Chart.functions_are_series p k d G c
  have hsq := chart_square_presents p k d G c
  obtain ⟨Bs, hBs, -⟩ := hfun.2.2 B.1 B.2
  obtain ⟨κ, hκ, -⟩ := hsq.2 cc.1 (fun n => (cc.2 n).2)
  have hlaw := (LawCoord.main p k d G c).2 μ hμ
  have hcoc : IsCoc μ κ := (isCoc_iff_mem_cocycles p k d G c μ hμ κ).2 (by
    have e : (fun n => c.ev₂ n κ) = cc.1 := funext hκ
    rw [e]; exact cc.2)
  have hmap := (isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (_root_.GlobalTheory.Katz.Chart.isMapOf_nmul p k d G c μ hμ p)
  have hid : cob1 μ Bs = pull2 (nmul μ p) κ := by
    obtain ⟨s, -, hs⟩ := hsq.2 (fun n => c.ev₂ n (cob1 μ Bs)) (fun n => hfun.2.1 n _)
    refine (hs _ fun n => rfl).trans (hs _ fun n => ?_).symm
    rw [(hmap.2 n).2, hκ, (hlaw.2 n Bs).2, hBs]
    exact (congrArg (fun z : G.cocycles => z.1 n) hcob).symm
  have hB0 : constantCoeff Bs = 0 := by
    have h := (counit_dUnit_evA k d (G.A 1) (c.x 1) (c.nil 1) (c.aug 1) Bs).1
    rw [← h]
    change Coalgebra.counit (R := k) (c.ev 1 Bs) = 0
    rw [hBs 1, hB1, hcounit]
  have hX : ∀ (σ : Type) (i : σ), constantCoeff (X i : MvPowerSeries σ k) = 0 :=
    fun _ i => constantCoeff_X i
  have hL : ∀ j, constantCoeff (inL (nmul μ p j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hR : ∀ j, constantCoeff (inR (nmul μ p j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hκ0 : constantCoeff κ = 0 := by
    have h1 := (SubstCalc.powerSeriesEvalTwoGroups_rules_alt k d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) _ _ hL hR).2.2.2.1 κ
    have h2 : constantCoeff (cob1 μ Bs) = 0 := by
      unfold cob1 inL inR
      rw [map_sub, map_sub, SubstCalc.constantCoeff_subst_of_zero hlaw.1,
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _),
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hB0, sub_zero, sub_zero]
    rw [← h1, ← h2, hid]
    rfl
  exact ⟨κ, Bs, hcoc, hκ0, hid, (hBs 1).trans hB1⟩

end GlobalTheory.Katz.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.GenTrait

theorem spMap_stalkHom_fromSpecStalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)
    (x : M.Z) : spMap (M.stalkHom x) ≫ M.Z.fromSpecStalk x = M.pt := by
  have e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
      Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by
    rw [RatModel.stalkHom]
    show Spec.map _ = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    rfl
  rw [e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt

end GlobalTheory.Poinc.GenTrait


open GlobalTheory.Poinc.GenTrait in
theorem GlobalTheory.Poinc.exists_trait_of_stalk_dvr : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp',
      Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubicalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framed_torsion_torus_extension_respect_cubical : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  first | exact @GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfGeneratingSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_of_generating_section : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R) (N : ℕ), 3 ≤ N → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GObj gb N s), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (exact GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one <;> assumption)
end

