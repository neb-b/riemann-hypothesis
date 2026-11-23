module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.DivP

open WithConv

variable {p : ℕ} {k : Type} [Field k]

theorem conv_eq_one_of_succ {G H : PDivGroup p k} (f : G ⟶ H) (n : ℕ) (h : f.conv (n + 1) = 1) :
    f.conv n = 1 := by
  have h1 : ∀ b, f.app (n + 1) b = algebraMap k _ (counit b) := fun b => by
    have := DFunLike.congr_fun (congrArg ofConv h) b
    simpa using this
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  change f.app n (H.res n b) = algebraMap k _ (counit (H.res n b))
  rw [← res_app, h1, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem conv_eq_one_of_le {G H : PDivGroup p k} (f : G ⟶ H) {m n : ℕ} (hmn : m ≤ n)
    (h : f.conv n = 1) : f.conv m = 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (conv_eq_one_of_succ f n h)

theorem app_kill {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) (n : ℕ) :
    ∀ {E : Type} [CommRing E] [Algebra k E] (x : G.A (n + 1) →ₐ[k] E), toConv x ^ p = 1 →
      ∀ c, x (f.app (n + 1) c) = algebraMap k E (counit c) := by
  induction n with
  | zero =>
    intro E _ _ x _ c
    have h1 : f.app 1 c = algebraMap k _ (counit c) := by
      have := DFunLike.congr_fun (congrArg ofConv hf) c
      simpa using this
    rw [h1, AlgHom.commutes]
  | succ n ih =>
    intro E _ _ x hx c
    have hx' : toConv x ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hx, one_pow]
    obtain ⟨y, hy⟩ := (G.exists_comp_res_iff (n + 1) x).2 hx'
    have hy' : toConv y ^ p = 1 := by
      have e : pointsMap E (G.res (n + 1)) (toConv y ^ p) = 1 := by
        rw [map_pow]
        change (toConv (y.comp (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)))) ^ p = 1
        rw [hy, hx]
      apply ofConv_injective
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := G.res_surjective (n + 1) a
      have e2 := DFunLike.congr_fun (congrArg ofConv e) b
      rw [ptsMap_ofConv, AlgHom.comp_apply] at e2
      refine e2.trans ?_
      show algebraMap k E (counit b) = algebraMap k E (counit (G.res (n + 1) b))
      rw [CoalgHomClass.counit_comp_apply]
    rw [← hy, AlgHom.comp_apply]
    change y (G.res (n + 1) (f.app (n + 2) c)) = _
    rw [res_app, ih y hy', CoalgHomClass.counit_comp_apply]

theorem exists_factor [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1)
    (n : ℕ) : ∃ g : H.A (n + 1) →ₐc[k] G.A n, ∀ b, G.mulP n (g b) = f.app (n + 1) b := by
  obtain ⟨r, hrs, hrk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  rw [pow_one] at hrk
  obtain ⟨B, _, _, _, _, j, hji, hjk, hjr⟩ := _root_.GlobalTheory.HopfQuot.exists_quotient k (G.A (n + 1)) (G.A 1) r hrs
  have hP : kerIdeal (G.mulP n) = RingHom.ker r := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res, hrk]
  have h1 : ∀ a, G.mulP n a ∈ Set.range j := hjr (G.A n) (G.mulP n) hP.le
  have hmk : toConv (Ideal.Quotient.mkₐ k (torsionIdeal (R := k) (A := G.A (n + 1)) p)) ^ p = 1 :=
    (torsionIdeal_le_ker_iff p _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 : ∀ b, f.app (n + 1) b ∈ Set.range j := by
    refine hjr (H.A (n + 1)) (f.app (n + 1)) ?_
    rw [hrk]
    intro a ha
    have := (kerIdeal_le_ker_iff (f.app (n + 1)) (Ideal.Quotient.mkₐ k _)).2
      (fun c => app_kill f hf n _ hmk c) ha
    rw [RingHom.mem_ker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  let jl := (j : B →ₐ[k] G.A (n + 1)).toLinearMap
  let ml := (G.mulP n : G.A n →ₐ[k] G.A (n + 1)).toLinearMap
  have hle : LinearMap.range ml ≤ LinearMap.range jl := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h1 a
    exact ⟨b, hb⟩
  have e1 := finrank_eq_ker_mul_range k (G.A (n + 1)) (G.A n) (G.mulP n)
  have e2 := finrank_eq_ker_mul_range k (G.A (n + 1)) B j
  rw [hP] at e1
  rw [hjk] at e2
  have hpos : 0 < Module.finrank k (G.A (n + 1) ⧸ RingHom.ker r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    have : Nontrivial (G.A (n + 1)) := (counitAlgHom k (G.A (n + 1))).domain_nontrivial
    have h3 := Module.finrank_pos (R := k) (M := G.A (n + 1))
    rw [e1, h0, zero_mul] at h3
    exact lt_irrefl _ h3
  have heq : LinearMap.range ml = LinearMap.range jl :=
    Submodule.eq_of_le_of_finrank_eq hle (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2))
  have h3 : ∀ b, f.app (n + 1) b ∈ Set.range (G.mulP n) := by
    intro b
    obtain ⟨c, hc⟩ := h2 b
    have : f.app (n + 1) b ∈ LinearMap.range ml := by
      rw [heq]
      exact ⟨c, hc⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective ml
    (LinearMap.ker_eq_bot.2 (Test.mulP_injective G n))
  exact GlobalTheory.bialgHom_factor_through_split k (G.A (n + 1)) (G.A n) (H.A (n + 1)) (G.mulP n) ρ
    (f.app (n + 1)) (fun a => LinearMap.congr_fun hρ a) h3

theorem exists_eq_p_smul [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  choose g' hg' using exists_factor f hf
  have hker : ∀ n, RingHom.ker (H.res n) ≤ RingHom.ker (g' n) := by
    intro n
    rw [H.ker_res]
    refine (kerIdeal_le_ker_iff _ (g' n : H.A (n + 1) →ₐ[k] G.A n)).2 fun c => ?_
    change g' n (mulBy k _ (p ^ n) c) = _
    rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]
  let gapp : ∀ n, H.A n →ₐc[k] G.A n := fun n =>
    liftSurj (H.res n) (H.res_surjective n) (g' n) (hker n)
  have hg : ∀ n b, gapp n (H.res n b) = g' n b := fun n b => liftSurj_apply ..
  have hcomm : ∀ n, (G.res n).comp (gapp (n + 1)) = (gapp n).comp (H.res n) := by
    intro n
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective (n + 1) a
    apply Test.mulP_injective G n
    change G.mulP n (G.res n (gapp (n + 1) (H.res (n + 1) b))) =
      G.mulP n (gapp n (H.res n (H.res (n + 1) b)))
    rw [hg, hg, mulP_res, hg' n, ← res_app, ← hg' (n + 1) b, res_mulP]
  refine ⟨⟨gapp, hcomm⟩, hom_ext_conv fun n => ?_⟩
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self n _)]
  have hfa : f.app n = (mulBy k (G.A n) p).comp (gapp n) := by
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective n a
    rw [← res_app, ← hg' n b, res_mulP, BialgHom.comp_apply, hg]
  change toConv (f.app n) = toConv (gapp n) ^ p
  rw [hfa, mulBy_comp, toConv_ofConv]

theorem conv_eq_one_of_p_smul [Fact p.Prime] {G H : PDivGroup p k} (g : G ⟶ H) (m : ℕ)
    (h : ((p : ℤ_[p]) • g).conv (m + 1) = 1) : g.conv m = 1 := by
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self _ _)] at h
  have h' : ∀ b, mulBy k (G.A (m + 1)) p (g.app (m + 1) b) = algebraMap k _ (counit b) := by
    intro b
    have e := DFunLike.congr_fun (congrArg ofConv h) b
    have e2 := DFunLike.congr_fun (mulBy_comp (g.app (m + 1)) p) b
    rw [BialgHom.comp_apply] at e2
    rw [e2]
    simpa using e
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective m a
  apply Test.mulP_injective G m
  change G.mulP m (g.app m (H.res m b)) = G.mulP m (algebraMap k _ (counit (H.res m b)))
  rw [← res_app, mulP_res, h', CoalgHomClass.counit_comp_apply]
  exact (AlgHomClass.commutes (G.mulP m) _).symm

theorem exists_eq_pow_smul [Fact p.Prime] {G H : PDivGroup p k} (m : ℕ) :
    ∀ f : G ⟶ H, f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  induction m with
  | zero => exact fun f _ => ⟨f, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    intro f hf
    obtain ⟨g, rfl⟩ := exists_eq_p_smul f (conv_eq_one_of_le f (by omega) hf)
    obtain ⟨g2, rfl⟩ := ih g (conv_eq_one_of_p_smul g m hf)
    exact ⟨g2, by rw [smul_smul, ← pow_succ']⟩

theorem divisible_of_conv_eq_one : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g :=
  fun _ _ _ _ _ _ _ m f hf => exists_eq_pow_smul m f hf

end GlobalTheory.PDivGroup.DivP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPointMapOfAdjointSplitUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
noncomputable section

namespace GlobalTheory.Mum.PowData

open GlobalTheory.Mum.FactorPol


set_option maxHeartbeats 1000000 in
theorem periodRel_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q inc j hinc hj iq adj qB h k L T
  have hA := hR.1
  have := hR.2
  have := U.gen_hom
  have := U₀.gen_hom
  haveI := hinc
  haveI := hj
  haveI : IsMonHom q := L.1
  obtain ⟨k', tk'⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  have un₀ := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have kh : ∀ χ, k' (h χ) = χ := congrFun ((un₀ _).2 _ _ (iq ▸ onTorus_comp tk' L.2.2.2) onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q qB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A₀.A, IsMonHom c ∧ Gen₀ U.toUnifPre U₀.toUnifPre q c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map q ≫ U₀.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨c', hc', gc'⟩ : ∃ c' : A₀.A ⟶ A.A, IsMonHom c' ∧ Gen₀ U₀.toUnifPre U.toUnifPre j c' :=
    ⟨U₀.gen.inv ≫ (Over.pullback (jK R)).map j ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  haveI := hc
  haveI := hc'
  obtain ⟨E, eG, eA⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (q ≫ j) (c ≫ c') inferInstance inferInstance
    (by
      unfold Gen₀ at gc gc'
      rw [Functor.map_comp, Category.assoc, gc', ← Category.assoc, gc, Category.assoc])
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB

  have lamE : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) (x ≫ q ≫ j) y = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [lam_comm, ← Category.assoc, adj, lam_comm]
  have lamE' : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) x (y ≫ q ≫ j) = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [← Category.assoc, adj]
  have adjE : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL _ _ _).trans (Eq.trans (by rw [eG, lamE, lamE']) (cls_cube_two hL _ _ _).symm))
  have H₂ : LBIso (cubeLB G₀ ![fst G G ≫ q, snd G G ≫ q] U₀.LG.L)
      (cubeLB G ![fst G G ≫ E.aG, snd G G ≫ 𝟙 G] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL₀ _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL₀ _ _ _).trans (Eq.trans (by rw [eG, Category.comp_id, lamE]) (cls_cube_two hL _ _ _).symm))
  have H₃ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q q E.aG (𝟙 _) c c E.aA (𝟙 _)
    gc gc E.ext (by simp [Gen₀]) H₂
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C E E adjE H₃
    Ω K

  have eh : (⇑E.h : D.toPre.X → D.toPre.X) = ⇑h ∘ ⇑k :=
    (un _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (onTorus_comp L.2.2.2 T)
  have hφk : ∀ y, φ y = k y := fun y => hinj ((hhφ y).trans (congrFun eh y))
  have hB := D.tau_bimult
  refine ⟨fun y => ?_, fun χ => ?_⟩
  · obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    rw [← hφk y]
    refine GlobalTheory.Mum.Two.Fac.pt_ext R D₀.toPre Ω _ _ ?_
    simpa only [Category.assoc] using h1
  · obtain ⟨u, hu, -⟩ := C χ
    refine ⟨u, hu, fun y z J hJ => ?_⟩
    obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have e := GlobalTheory.Mum.Two.act_val_frac R D₀.toPre D.toPre qB h Ω y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha χ u hu
      z J hJ
    rwa [hφk] at e

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEulerFactorOfRamified
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypotheses
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRefPt

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem exists_root_of_isNorm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {ν ν' : ℂ}
    (hN : IsNorm Rl v₀ B ν) (hN' : IsNorm Rl v₀ B ν') : ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ ν' = ζ * ν := by
  obtain ⟨h0, c, hc, n, hn, hνn⟩ := hN
  obtain ⟨-, c', hc', m, hm, hν'm⟩ := hN'
  obtain ⟨k, hk, hkk⟩ := isScale_pow_eq Rl v₀ _ hc hc'
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  have e4 : ν' ^ (n * m * k) = ν ^ (n * m * k) := by
    rw [e1, e2, hν'm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
      show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
  refine ⟨ν' / ν, isAlgebraic_of_pow_eq_one (Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk) ?_, (div_mul_cancel₀ ν' h0).symm⟩
  rw [div_pow, e4, div_self (pow_ne_zero _ h0)]

theorem theta_eq_zero {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) {ν : ℂ} (h0 : ∀ x ∈ (Rl.FW j).WK, x = 0) (hR : RatBase (realRd YS v₀ hρ i j b ν))
    {s : Finset (Pl D.host.E)} {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hd : ρ.IsDatum i j b s h P) :
    ρ.theta i j b h P = 0 := by
  have hW : ∀ g : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j g.val = 0 := fun g => by
    have h1 : (YS.fi j).e g.val = 0 := h0 _ (((YS.fi j).wk _).1 g.2)
    have h2 : g.val = 0 := (YS.fi j).e.injective (h1.trans (map_zero _).symm)
    rw [h2, map_zero]
  have hK : ∀ x, evK YS v₀ hρ i j b x = 0 := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | tmul a g => rw [evK_tmul, hW, smul_zero]
  obtain ⟨f, hf⟩ := hR s h P hd
  rw [← hf]
  change ν⁻¹ • evK YS v₀ hρ i j b _ = 0
  exact (congrArg (ν⁻¹ • ·) (hK _)).trans (smul_zero _)

theorem algComb_of_moved {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    {φ : GA D (Wc D j) → ℂ} (h : AlgComb (GlobalTheory.UnframeForms.movedYS YS w) v₀ j φ) : AlgComb YS v₀ j φ := by
  obtain ⟨n, z, g, hz, e⟩ := h
  refine ⟨n, z, fun k => (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A)))
      (show ↥(S.A ((j : ℕ) + 1)).WK from g k).1,
    YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from g k).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), hz, ?_⟩
  rw [e]
  exact Finset.sum_congr rfl fun k _ => congrArg (z k • ·) (GlobalTheory.UnframeForms.evW_moved YS w v₀ j _)

theorem core_cases (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt) (hS : GlobalTheory.SerStd.SeriesRatS)
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw}
    {j : Fin D.R.m} (b : Bool) {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hpin : RealPin Rl cG ρ) (H : RatHyp T Rl F κ v₀ O i j hV)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) :
    (∀ x ∈ (Rl.FW j).WK, x = 0) ∨ ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ ∀ s h P, ρ.IsDatum i j b s h P →
      P ∈ ρ.lat i j b (smallInt D) h → AlgComb YS v₀ j (ν • ρ.theta i j b h P) := by
  obtain ⟨fw⟩ := H.fw
  by_cases hc : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine Or.inl fun x hx => ?_
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨x, hx⟩
    have h0 : f = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hc f.1 f.2)
    rw [h0, map_zero] at hf
    exact (congrArg Subtype.val hf).symm
  · obtain ⟨ν, hN, hν⟩ := _root_.GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std hA hRF hS D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hc
    exact Or.inr ⟨ν, hN, algComb_of_ratScalar YS hRF fw (fw.evaluates_of_lUnif H.unif) H.core H.io
      (GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat H.laws.toLawsM H.core.lev (H.pins.2.tuple ()).half)
      H.size H.galois H.small.val H.small.ray H.small.roots hsp hρ hpin i j b hV hν⟩

end Core

end GlobalTheory.SerRefPt

namespace GlobalTheory.SerRefPt

open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt


end GlobalTheory.SerRefPt
end
end

