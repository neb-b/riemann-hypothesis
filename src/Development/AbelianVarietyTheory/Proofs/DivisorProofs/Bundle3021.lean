module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsProjectivelyIntegralNormalModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThInt

theorem spMap_comp_ring' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self' {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp' {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq' (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr' {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thList_pull_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec G))} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {K : Type} [Field K]
    (x : Sp R ⟶ S) (θ : SecAt G L x) (i : R →+* R') (j : R' →+* K) {N : ℕ}
    {pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap (j.comp i) ≫ x) ⟶ G), ThList G L ρ m (spMap (j.comp i) ≫ x)
      (SecAt.pull G L θ (j.comp i)) pt' c := by
  simp only [SecAt.pull] at H ⊢
  rw [pullS_comp' G hL] at H
  refine thList_congr' θ (by rw [← Category.assoc, spMap_comp_ring']) _ _ ?_ H
  simp only [Over.comp_left, Over.homMk_left]
  rw [spMap_comp_ring']

end GlobalTheory.UMin.ThInt

namespace GlobalTheory.UMin


open GlobalTheory.UMin.ThInt in
theorem thetaInt_hasDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf o' Ω _ _ _ _ S ρ u hu M g hnorm hg
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI : IsAbelianScheme ρ.P.A := ρ.P.isAb
  haveI : IsCommMonObj ρ.P.A := IsAbelianScheme.comm
  set gd := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgd
  let vH : ratHull S.R →+* Ω := (ratHull S.R).val.toRingHom
  let v : S.R →+* Ω := S.R.val.toRingHom
  have hv : vH.comp (toRat S.R) = v := RingHom.ext fun _ => rfl
  let x₀ : Sp Ω ⟶ Sp S.R := spMap v ≫ 𝟙 (Sp S.R)
  let θ : SecAt ρ.P.A ρ.P.L x₀ := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o' Ω S ρ Ω v
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := hu
  haveI : IsAbelianScheme G := PolPull.isAbelianScheme_of_isGrpPullback ρ.P.isAb hα
  haveI : IsCommMonObj G := IsAbelianScheme.comm
  have hLG : (ρ.P.L.pull α).IsLB := pull_isLB ρ.P.isLB α
  have hU := Xo.univ.t.PP.isLB
  have hUr := Xo.univ.t.PP.rigGen

  have hdim := GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (spMap vH ≫ u ≫ pullback.fst _ _)
  have hmv1 := _root_.GlobalTheory.UMin.FibMove.polFib_move Xo.X (Sp (ratHull S.R)) Xo.univ.t.G Xo.univ.t.PP.L G (ρ.P.L.pull α) (u ≫ pullback.fst _ _) β
    hU hLG hβ hL gd Ω (spMap vH)
  have hmv2 := _root_.GlobalTheory.UMin.FibMove.polFib_move (Sp S.R) (Sp (ratHull S.R)) ρ.P.A ρ.P.L G (ρ.P.L.pull α) (spMap (toRat S.R)) α
    ρ.P.isLB hLG hα (PolBaseChange.lbIso_refl hLG) gd Ω (spMap vH)
  have hPG : PolFib G (ρ.P.L.pull α) gd (spMap vH) := hmv1.1.2 hdim
  have hPF : PolFib ρ.P.A ρ.P.L gd x₀ := by
    have h := hmv2.1.1 hPG
    rwa [spMap_comp_ring', hv, ← Category.comp_id (spMap v)] at h

  obtain ⟨e, he⟩ := _root_.GlobalTheory.UMin.SymRat.symAt_exists (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) Ω x₀ θ hm hn hPF

  obtain ⟨P', φG, hgP, hφG, hφGL⟩ := hPG
  have hPL : P'.L.IsLB := P'.isLB
  have hφGα : IsGrpPullback P'.A ρ.P.A x₀ (φG ≫ α) :=
    (hφG.comp hα).congr (by rw [spMap_comp_ring', hv]; exact (Category.comp_id _).symm) rfl
  have hφGβ : IsGrpPullback P'.A Xo.univ.t.G ((spMap vH ≫ u) ≫ pullback.fst _ _) (φG ≫ β) :=
    (hφG.comp hβ).congr (by rw [Category.assoc]) rfl
  have hLα : LBIso P'.L (ρ.P.L.pull (φG ≫ α)) :=
    LBIso.trans hPL (pull_isLB hLG φG) (pull_isLB ρ.P.isLB _) hφGL
      (GenSpread.lbIso_pull_of_lbIso (PolBaseChange.lbIso_refl hLG) φG rfl)
  have hLβ : LBIso P'.L (Xo.univ.t.PP.L.pull (φG ≫ β)) :=
    LBIso.trans hPL (pull_isLB ρ.P.isLB _) (pull_isLB hU _) hLα (GenSpread.lbIso_pull_comp φG rfl rfl hL)
  have hcrd := _root_.GlobalTheory.UMin.pCrd_of_symAt Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr gd m n o (Xo.XF c)
    (pullback.fst _ _) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig Ω (spMap vH ≫ u) x₀ P' (φG ≫ β) (φG ≫ α) θ e hm hn hf
    ρ.P.isLB ρ.rig_gen hgP hφGβ hLβ hφGα hLα hθ he
  have hdiv : M.HasDiv e := by
    refine _root_.GlobalTheory.UMin.hasDiv_of_pCrd_pt o' Ω o M n g e ?_
    rw [hg, ← Category.assoc]
    exact hcrd

  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hkodd : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)
  have hk3 : 3 ≤ S.r * S.N := by
    have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
    obtain ⟨t, ht⟩ := hkodd
    omega
  refine _root_.GlobalTheory.ValCmp.hasDiv_of_forall_cDvr o' Ω M S.Gam (Fin (n + 1)) S.th e (n + 1).factorial (Nat.factorial_pos _) hnorm hdiv ?_
  intro V _ _ _ hV ξ emb _ j₀ hj₀ hej
  haveI : IsDiscreteValuationRing V := hV.1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : Ω →+* K := io.comp emb
  have hcast : ∀ t : ℕ, t ≠ 0 → (t : K) ≠ 0 := fun t ht => by
    rw [← map_natCast i t]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ht)
  have hmV : IsUnit (m : V) := by
    simpa using hmu.map (Spec.preimage (ξ ≫ g ≫ PSpace.str o n)).hom
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := by
    simpa using S.unit.map (Spec.preimage (ξ ≫ M.s)).hom

  have hPK : PolFib ρ.P.A ρ.P.L gd (spMap i ≫ x₀) :=
    (_root_.GlobalTheory.UMin.FibMove.polFib_move (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self' _)
      (ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) gd Ω x₀).2 K i hPF
  have hθK := (_root_.GlobalTheory.UMin.gen_of_polFib (Sp S.R) ρ.P.A ρ.P.L ρ.P.isLB gd Ω x₀ hPF).2 θ hθ K i
  obtain ⟨pt, d, hd⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) K (spMap i ≫ x₀)
    (SecAt.pull ρ.P.A ρ.P.L θ i) hm (hcast m hm.pos.ne') hn hPK
  obtain ⟨pt', d', hd'⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd (S.r * S.N)
    ((S.r * S.N) ^ (4 * gd)) K (spMap i ≫ x₀) (SecAt.pull ρ.P.A ρ.P.L θ i) hkodd (hcast _ (NeZero.ne _)) rfl hPK
  have hsym : ∀ j, io (emb (e j)) = symTup d j := he K i pt d hd
  obtain ⟨pt'', hd''⟩ := thList_pull_pull ρ.P.isLB (𝟙 (Sp S.R)) ρ.th₁ v i hd'
  have hT := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o' Ω S ρ K (i.comp v) _ pt'' d' hd''

  have h₁ : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ x₀) d d' := ⟨_, pt, pt', hθK, hd, hd'⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hLG
  obtain ⟨ρG, hρG, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw ρ.P.isLB hLG ρ.rig_gen
  let xV : Sp K ⟶ Sp (ratHull S.R) := spMap io ≫ spMap emb ≫ spMap vH
  have hxV : spMap i ≫ x₀ = xV ≫ spMap (toRat S.R) := by
    simp only [xV, x₀, i, Category.comp_id, Category.assoc, spMap_comp_ring', ← hv, RingHom.comp_assoc]
  rw [hxV] at h₁
  have h₂ := (_root_.GlobalTheory.UMin.ThMove.hasTh₂_move (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (spMap (toRat S.R)) α hLG hρG hα (PolBaseChange.lbIso_refl hLG) m (S.r * S.N) (n + 1) _ K xV d d').2 h₁
  have h₃ := (_root_.GlobalTheory.UMin.ThMove.hasTh₂_move Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (u ≫ pullback.fst _ _) β hLG hρG hβ hL m (S.r * S.N) (n + 1) _ K xV d d').1 h₂
  let y : Sp (FractionRing V) ⟶ Xo.XF c := spMap emb ≫ spMap vH ≫ u
  have h₄ : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (S.r * S.N) (spMap io ≫ y ≫ pullback.fst _ _) d d' := by
    have e₄ : spMap io ≫ y ≫ pullback.fst _ _ = xV ≫ u ≫ pullback.fst _ _ := by
      simp only [xV, y, Category.assoc]
    rw [e₄]
    exact h₃
  obtain ⟨a, ha, hPa, hPa'⟩ := _root_.GlobalTheory.UMin.CmpTrait.cmp_trait E H Dw l Xo c V hV y K io m (S.r * S.N) (n + 1) _ d d' hm hm3 hmV hkodd hk3
    hkV h₄
  have hP := _root_.GlobalTheory.UMin.prim_symTup_cmp V K io (n + 1) _ ((S.r * S.N) ^ 2) S.Gam d d' a (fun j => emb (e j)) (fun b => emb (S.th b)) ha
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))) hPa hPa' hsym hT.1 hT.2 j₀ ((map_ne_zero emb).2 hj₀)
    (fun j => by simpa [map_div₀] using hej j)
  refine ⟨fun b => by simpa [map_div₀, map_pow] using hP.1 b, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hP.2
  exact ⟨b, fun h0 => hb (by simp [h0]), by simpa [map_div₀, map_pow] using hb'⟩

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG.ThetaVal

open GlobalTheory.USep.EvG

theorem one_left' {S X : Scheme.{0}} (G : Over S) [GrpObj G] (t : X ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  rw [Hom.one_def]; rfl

theorem toUnit_eta_left {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (toUnit G ≫ η[G]).left = G.hom ≫ (η[G]).left := by
  rfl

@[reassoc]
theorem spMap_two' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem eta_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) : (toUnit G' ≫ η[G']).left ≫ F = G'.hom ≫ f ≫ (η[G]).left := by
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hF G'.hom (G'.hom ≫ f) rfl
  have h1 := he 1
  rw [map_one, one_left', one_left'] at h1
  rw [toUnit_eta_left, ← h1, Category.assoc]

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

theorem famφB_one (D : DegPre V₁) : D.famφB 0 1 = 𝟙 _ := by
  have h : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0) = 𝟙 D.P.A := by
    rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
    exact mul_one (𝟙 D.P.A)
  show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
  rw [h]; rfl

theorem famφB_two (D : DegPre V₁) : D.famφB 0 2 = D.famφB 0 3 := by
  show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
  rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
  rfl

def chartPullCompPull {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun k => φ k ≫ F) ε) (LB.LinComb (L.pull F) φ ε) (𝟙 Y) :=
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart (L.pull F) φ (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun k => φ k ≫ F) ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).symm
      simp only [Category.assoc] }

theorem gm_linCombIso_pull' {A A₂ Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (w : LB.Iso L₂ (L.pull φ))
    {K : Type} [Fintype K] (φ' : K → (Y₂ ⟶ A₂)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y₂) (z : Z) (p : K → L.ι) (q : K → L₂.ι)
    (hm : r z ∈ LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q) :
    gm r z (LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q)
      ((LB.linCombIso w φ' ε).s (fun k _ => p k, q)) = ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ' k) z ((L.pull φ).U (fun _ => p k) ⊓ L₂.U (q k))
    ⟨Set.mem_iInter.1 hm.1 k, Set.mem_iInter.1 hm.2 k⟩ _)

theorem exists_conj_fibre_one {V₁ W₀ : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] (D : DegPre V₁) (ib : W₀ →+* V₁)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : D.P.A.left ⟶ B₀.left) (hβ : IsGrpPullback D.P.A B₀ (spMap ib) β)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ib a) ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt : (Over.mk (spMap ev) ⊗ D.P.A).left ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left,
      σt ≫ (fst (Over.mk (spMap ev)) D.P.A).left = (fst (Over.mk (spMap ev)) D.P.A).left ≫ spMap σ.toRingHom ∧
      σt ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β = (snd (Over.mk (spMap ev)) D.P.A).left ≫ β ∧
      ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
        DefOver k₀ (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β) → x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E D.P.A).left with hfK
  set q := (snd E D.P.A).left with hq
  have hw : q ≫ D.P.A.hom = fK ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib)) (by rw [Category.assoc, spMap_two'])
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap σ.toRingHom ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib))
    (by rw [Category.assoc, Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ D.P.A := Over.homMk q hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ D.P.A).left ⟶ (E ⊗ D.P.A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ q = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : σt ≫ q ≫ β = q ≫ β := by
    rw [reassoc_of% hsnd, ← hΦ₁ σD, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, hfst, hproj, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ D.P.A).hom = fK ≫ spMap ev := (Over.w (fst E D.P.A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ D.P.A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ D.P.A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ
        (spMap σ.toRingHom ≫ spMap ev) (spMap (ev.comp ib))
        (by rw [Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show (x ≫ σt) ≫ q ≫ β = (spMap σ.toRingHom ≫ x) ≫ q ≫ β
      obtain ⟨P₀, hP₀⟩ := hdef
      rw [Category.assoc, hproj, Category.assoc, ← hP₀, ← Category.assoc,
        spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem gm_thetaIso {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) {B₀ : Scheme.{0}} {M₀ : LB B₀}
    (β : D.P.A.left ⟶ B₀) (w : LB.Iso D.P.L (M₀.pull β)) {K : Type} [Field K] (r : Sp K ⟶ D.P.A.left) (z : Sp K)
    (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀) → M₀.ι) (hJ : Good D.P.L z J) (hJ₀ : Good M₀ z J₀) :
    gm r z _ ((GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))).s
        (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)), fun k => J (r ≫ D.famφB 0 k))) = gwx w z J J₀ r := by
  have hz : r z ∈ (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).U (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨hJ₀.mem (fun k => D.famφB 0 k ≫ β) r, hJ.mem (D.famφB 0) r⟩
  refine (GlobalTheory.PolDeg.TautFrom.gm_isoPull _ _ _ r z _ hz).trans ?_
  rw [Category.comp_id]
  have hm : r z ∈ LB.wchart (M₀.pull β) (D.famφB 0) (fun k _ => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      LB.wchart D.P.L (D.famφB 0) (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hz.1 k), hz.2⟩
  refine (gm_linCombIso_pull' w (D.famφB 0) (DegPre.famε 1) r z (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)))
    (fun k => J (r ≫ D.famφB 0 k)) hm).trans ?_
  have h0 : D.famφB 0 0 = 𝟙 _ := rfl
  rw [Fin.prod_univ_four, h0, famφB_one D, famφB_two D]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_one, zpow_neg, one_mul,
    Category.comp_id, Category.id_comp, mul_inv_cancel_right]
  rw [_root_.one_mul, inv_mul_cancel_right]

theorem theta_values : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ θ hθ
  obtain ⟨-, hM₀, hβ, hw, -, -, -⟩ := hFB
  let u := GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))
  have hu : u.IsGen := GlobalTheory.PolDeg.TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen w hw _ _)
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ hM₀ _ _
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_isoRel hL hM hu
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  have hqw : q ≫ D.P.A.hom = (fst E D.P.A).left ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  let R : (Sp K ⟶ (E ⊗ D.P.A).left) → Prop := fun x => x ≫ (fst E D.P.A).left = 𝟙 _ ∧ DefOver k₀ (x ≫ q ≫ β)
  have hcases : ∀ k : Fin 4, D.famφB 0 k = 𝟙 _ ∨ D.famφB 0 k ≫ β = D.P.A.hom ≫ spMap ib ≫ (η[B₀]).left := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inl (by show D.famφB 0 1 = _; exact famφB_one D)
    · exact Or.inr (by show D.famφB 0 2 ≫ β = _; rw [famφB_two D]; exact eta_push hβ)
    · exact Or.inr (by show D.famφB 0 3 ≫ β = _; exact eta_push hβ)
  obtain ⟨κ, -, hval⟩ := galois_values k₀ hk₀ (fun k => q ≫ (D.famφB 0 k ≫ β)) (DegPre.famε 1)
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s q) R
    (fun t => by
      obtain ⟨c, hc⟩ := fibre_one_dim D ev (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (hθ K ev)
        (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1) hM₀ u hu s hs t
      exact ⟨c, fun x hR z J hJ => hc x hR.1 z J hJ⟩)
    (fun σ hσ => by
      obtain ⟨σt, hfst, hproj, hfix⟩ := exists_conj_fibre_one D ib B₀ β hβ K ev k₀ hk σ hσ
      refine ⟨σt, fun k => ?_, fun x hR => hfix x hR.1 hR.2⟩
      rcases hcases k with h | h
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        rw [h, Category.id_comp]
        exact hproj
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
        rw [h, reassoc_of% hqw, reassoc_of% hfst, spMap_two'_assoc ib ev, reassoc_of% (spMap_conj k₀ _ hf σ hσ)])
  refine ⟨κ, fun p hdef => ?_⟩
  have hr : (spMap ev ≫ p.left) ≫ D.P.A.hom = spMap ev := by
    rw [Category.assoc, Over.w p]
    exact Category.comp_id _
  let a1 : Over.mk (spMap ev) ⟶ E := Over.homMk (𝟙 (Sp K)) (Category.id_comp _)
  let b1 : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (spMap ev ≫ p.left) hr
  let x : Sp K ⟶ (E ⊗ D.P.A).left := (lift a1 b1).left
  have hxf : x ≫ (fst E D.P.A).left = 𝟙 _ :=
    congrArg (fun m : Over.mk (spMap ev) ⟶ E => m.left) (lift_fst a1 b1)
  have hxq : x ≫ q = spMap ev ≫ p.left := congrArg (fun m : Over.mk (spMap ev) ⟶ D.P.A => m.left) (lift_snd a1 b1)
  have hRx : R x := ⟨hxf, by
    show DefOver k₀ (x ≫ q ≫ β)
    rw [reassoc_of% hxq]
    exact hdef⟩
  obtain ⟨c, hc, he⟩ := hval x hRx z J₀ hJ₀
  refine ⟨c, hc, ?_⟩
  have e1 : sval s (spMap ev ≫ p.left) z J₀ = toStk z (κ * c) := by
    rw [← he, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ₀, hxq]
  have e2 := gs_isoRel_at hs _ _ (spMap ev ≫ p.left) z (hJ₀.mem (fun k => D.famφB 0 k ≫ β) (spMap ev ≫ p.left))
    (hJ.mem (D.famφB 0) (spMap ev ≫ p.left))
  rw [gm_thetaIso D β w (spMap ev ≫ p.left) z J J₀ hJ hJ₀] at e2
  have e4 : (gwx w z J J₀ (spMap ev ≫ p.left)).val *
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J = toStk z (κ * c) := by
    rw [← e1]; exact e2.symm
  rw [← e4, Units.inv_mul_cancel_left]

end GlobalTheory.USep.EvG.ThetaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTorsionRigidOverModuliFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorsRigid

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem torsion_rigid : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K L : Type) [Field K] [Field L] (y : Sp K ⟶ Xo.XF c) (x : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∀ κ₁ κ₂ : Sp L ⟶ Sp K, κ₁ ≫ y = κ₂ ≫ y → κ₁ ≫ x.left = κ₂ ≫ x.left := by
  intro E _ _ _ H Dw l Xo c φ K L _ _ y x hx κ₁ κ₂ hκ
  obtain ⟨⟨p, ψ⟩, hyp⟩ := (Scheme.SpecToEquivOfField K (Xo.XF c)).symm.surjective y
  let k : Type := (Xo.XF c).residueField p
  let y₀ : Sp k ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField p
  let φ' : k →+* K := ψ.hom
  have hy : y = spMap φ' ≫ y₀ := hyp.symm
  let K' := AlgebraicClosure K
  let ιK : K →+* K' := algebraMap K K'
  haveI := epi_spMap_field ιK
  let j : Over.mk (spMap (ιK.comp φ') ≫ y₀ ≫ pullback.fst _ _) ⟶
      Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap ιK) (by
      simp only [Over.mk_hom, hy, Category.assoc]
      rw [← Category.assoc (spMap ιK), ← spMap_comp])
  have hx' : (j ≫ x) ^ l.M' = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨x₀, -, hx₀⟩ := _root_.GlobalTheory.XFTorsion.torsion_rational Xo c φ k K' (ιK.comp φ') y₀ (j ≫ x) hx'
  have hxl : x.left = spMap φ' ≫ x₀.left := by
    rw [← cancel_epi (spMap ιK)]
    have : spMap ιK ≫ x.left = spMap (ιK.comp φ') ≫ x₀.left := hx₀
    rw [this, ← Category.assoc, ← spMap_comp]
  have hκ' : κ₁ ≫ spMap φ' = κ₂ ≫ spMap φ' := by
    rw [← cancel_mono y₀]
    simpa only [hy, Category.assoc] using hκ
  rw [hxl, ← Category.assoc, hκ', Category.assoc]

end GlobalTheory.TorsRigid
end
end

