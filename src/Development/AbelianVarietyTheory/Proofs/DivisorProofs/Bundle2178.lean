module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorsionTransfer

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (m : ℕ) :
    (x ^ m).left = (x' ^ m).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem fixed_of_jointlyMonic : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro V W _ _ _ _ io F _ _ _ hF G _ H _ r hr hmono σ hσ m hfix x hx
  have hT : spMap σ.toRingHom ≫ (TF (R := W) F).hom = (TF (R := W) F).hom := by
    show Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext w
    exact hσ w
  have hV : (TF (R := W) F).hom ≫ spMap io = (TF (R := V) F).hom := by
    show (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext v
    exact hF v
  have hpb := isGrpPullback_pullback G (spMap io)
  let x' : TF (R := W) F ⟶ H := Over.homMk (spMap σ.toRingHom ≫ x.left) (by
    rw [Category.assoc, Over.w x]; exact hT)
  have key : ∀ k, x' ≫ r k = x ≫ r k := by
    intro k
    have hk := hr k
    let z := x ≫ r k
    have hs : z.left ≫ pullback.snd G.hom (spMap io) = (TF (R := W) F).hom := Over.w z
    let y : TF (R := V) F ⟶ G := Over.homMk (z.left ≫ pullback.fst G.hom (spMap io)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact hV)
    let ρ : (TF (R := W) F ⟶ H) →* (TF (R := W) F ⟶ (Over.pullback (spMap io)).obj G) :=
      MonoidHom.mk' (fun u => u ≫ r k) fun u v => MonObj.mul_comp u v (r k)
    have hzm : z ^ m = 1 := by
      have e := map_pow ρ x m
      rw [hx, map_one] at e
      exact e.symm
    have hym : y ^ m = 1 := by
      apply Over.OverMorphism.ext
      have e1 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl m
      rw [← map_pow, hzm, map_one] at e1
      have e0 := pow_left_congr hV.symm y (pushHom hpb _ z) rfl 0
      simp only [pow_zero] at e0
      rw [e1, e0]
    have hfy := hfix y hym
    apply Over.OverMorphism.ext
    show (spMap σ.toRingHom ≫ x.left) ≫ (r k).left = x.left ≫ (r k).left
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact hfy
    · rw [Category.assoc, Category.assoc]
      change spMap σ.toRingHom ≫ z.left ≫ _ = z.left ≫ _
      rw [hs, hT]
  exact congrArg (fun u => u.left) (hmono _ x' x key)

end GlobalTheory.TorsionTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames frX frVec)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem tv_vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X}
    (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx
  rfl

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (Q Q' : FrPt Xo c S)
    (e : Q'.x = Q.x) : ∃ u : Sˣ, ∀ e : Q'.x = Q.x, ∀ i, (e ▸ Q'.s).f i = scal Q.x (u : S) i * Q.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨u0, fun _ => hu0⟩

theorem rel_unique : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  intro E _ _ _ H Dw l Xo c Y X C _ hC K _ z z' p hp hr hr'
  obtain ⟨φ, k, hk, g, hφ, hg, hc⟩ := hr
  obtain ⟨φ', k', hk', g', hφ', hg', hc'⟩ := hr'
  have e1 : p ≫ C.π ≫ genι Y = z ≫ X.π := carries_over C hc
  have e2 : p ≫ C.π ≫ genι Y = z' ≫ X.π := carries_over C hc'
  have hπ : z' ≫ X.π = z ≫ X.π := e2.symm.trans e1
  have ephi : φ' = φ := by
    have h0 : spMap φ' = spMap φ := by rw [← hφ', ← hφ, ← Category.assoc, hπ, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst ephi
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ' (z ≫ X.π), ∀ τ i, g0.v τ i = g'.v τ i := by
    rw [← hπ]; exact ⟨g', fun _ _ => rfl⟩
  have hc0 : C.Carries p g0 := (carries_congr C hπ.symm g0 g' hg0 p).2 hc'
  obtain ⟨t, ht⟩ := hC K _ _ (z ≫ X.π) p g g0 hc hc0
  letI : Algebra c.F K := φ'.toAlgebra
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hxg : (p ≫ C.π) ≫ genι Y = z ≫ X.π := by rw [Category.assoc]; exact e1
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have := hp a
    rw [Scheme.Hom.comp_apply]
    exact this
  have := Y.jQ_open
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy0 : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hyj : z ≫ X.π = y ≫ Y.j := by
    rw [Model.j, ← Category.assoc, hy0, ← hxg]
  have hstr : genStr Y = genι Y ≫ Y.s := by
    calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← Y.jQ_over, ← Category.assoc, hy0]
    show (p ≫ C.π) ≫ genStr Y = _
    rw [hstr, ← Category.assoc, hxg, Category.assoc]
    exact hφ
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hyj k hk
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr hy (hπ.trans hyj) k' hk'
  have hx : frX Q ≫ Y.j = z ≫ X.π := hQ.over
  have hx' : frX Q' ≫ Y.j = z ≫ X.π := hQ'.over.trans hπ
  have eQ : Q'.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := Y) (GlobalTheory.FlagMod.frX_snd Q') (GlobalTheory.FlagMod.frX_snd Q) (hx'.trans hx.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q Q' eQ
  choose cf hcf1 hcf2 hcf3 using ht.2.2
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  let T : Ix Dw → Kˣ := fun ix => match ix with | none => u0 | some q => t q.1 q.2
  have hB : FrBor T Q Q' := by
    refine GlobalTheory.FlagMod.frBor_of_frVec (X.F.inM hk rfl) hx hx' T (fun σ j i => cf σ i j)
      (fun σ r s hrs => hcf2 σ s r hrs) (fun σ i => hcf1 σ i) (fun σ i => ?_) hu0
    rw [hQ'.frVec_eq hπ hx', hQ.frVec_eq rfl hx]
    refine (GlobalTheory.LieMet.isComb_iff _ _ _).1 ?_
    have h3 := hcf3 σ i
    simp only [h1, Category.id_comp] at h3
    rw [hg0 σ i, hg' σ i, ← tv_vecAt_congr X.F k' z' hk' hπ σ i] at h3
    have e : (fun j => g.v σ j) = fun j => (tv (X.F.vecAt k z hk rfl σ j)).left := funext (hg σ)
    rw [e] at h3
    exact h3
  exact (X.rep K Q').unique (hQ.lies.frBor hB) hQ'.lies

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnOfPreimageMemSpanBy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_appLE_top (D : Type) [CommRing D] {X' : Scheme.{0}} [IsIntegral X'] (p' : X' ⟶ Sp D) (V : X'.Opens)
    (hV : genericPoint X' ∈ V) (h : V ≤ p' ⁻¹ᵁ ⊤) (z : Γ(Sp D, ⊤)) :
    fnOf V hV ((p'.appLE ⊤ V h) z) = fnOf ⊤ trivial (p'.appTop z) := by
  rw [← Scheme.Hom.appLE_map p' (U := ⊤) (V := ⊤) (by simp) (homOfLE (le_top : V ≤ ⊤)).op]
  rw [CommRingCat.comp_apply]
  refine (X'.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) _ hV ((p'.appLE ⊤ ⊤ (by simp)) z)).trans ?_
  have e : p'.appLE ⊤ ⊤ (by simp) = p'.appTop := (Scheme.Hom.app_eq_appLE p').symm
  rw [e]
  rfl

theorem fnOf_preimage_mem_spanBy : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp T) (p' : X' ⟶ Sp D) (π : X' ⟶ X) (θ : X.functionField →+* X'.functionField), IsPullback π p' p (spMap a) → PFF (𝟙 _) π θ → ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint X' ∈ π ⁻¹ᵁ U), IsAffineOpen U → ∀ s : Γ(X', π ⁻¹ᵁ U), GlobalTheory.Cartier.fnOf (π ⁻¹ᵁ U) hU' s ∈ spanBy (GlobalTheory.Desc.cst p') (θ '' Set.range (GlobalTheory.Cartier.fnOf U hU)) := by
  intro T D _ _ a X X' _ _ p p' π θ H hθ U hU hU' hAff s
  letI : Algebra D X'.functionField := (GlobalTheory.Desc.cst p').toAlgebra
  set M : Submonoid X'.functionField := ((θ.comp (fnOf U hU)).rangeS).toSubmonoid with hM
  have hMset : (M : Set X'.functionField) = θ '' Set.range (fnOf U hU) := by
    ext v; simp [hM, Set.range_comp]
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hAff)
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let S : Subring Γ(X', π ⁻¹ᵁ U) := (Algebra.adjoin D (M : Set X'.functionField)).toSubring.comap (fnOf (π ⁻¹ᵁ U) hU')
  have hle : (⊤ : Subring _) ≤ S := by
    rw [← hcl, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      apply Algebra.subset_adjoin
      rw [hMset]
      refine ⟨fnOf U hU y, ⟨y, rfl⟩, ?_⟩
      rw [GaussPt.theta_fnOf hθ U hU hU', Scheme.Hom.app_eq_appLE]
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      have e : fnOf (π ⁻¹ᵁ U) hU' ((p'.appLE ⊤ (π ⁻¹ᵁ U) (by simp)) z) = algebraMap D X'.functionField ((Scheme.ΓSpecIso (CommRingCat.of D)).hom z) := by
        rw [RingHom.algebraMap_toAlgebra]
        simp only [GlobalTheory.Desc.cst, RingHom.comp_apply]
        refine (fnOf_appLE_top D p' _ hU' _ z).trans ?_
        simp
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
  have hs : fnOf (π ⁻¹ᵁ U) hU' s ∈ Algebra.adjoin D (M : Set X'.functionField) := hle (Subring.mem_top s)
  have hsp : fnOf (π ⁻¹ᵁ U) hU' s ∈ Submodule.span D (M : Set X'.functionField) := by
    have := Algebra.adjoin_eq_span D (M : Set X'.functionField)
    rw [Submonoid.closure_eq] at this
    rw [← this]; exact hs
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hsp
  refine ⟨n, f, fun i => g i, fun i => hMset ▸ (g i).2, ?_⟩
  rw [← hfg]
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalForm
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.formOrd_eq_mult_of_isDivOfForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = K.mult w := by
  intro k _ _ Y _ _ q n _ η hη K hK E w hE
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n ‹_›
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame q n w
  have hgen := isFreeGen_formOf (gen_mem hU) hω
  have h0 : formOf U (gen_mem hU) ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun e => hη (by rw [← hc, e]; exact zero_smul _ _)
  have h1 := hK U ω hω w hU (Units.mk0 c hc0) hc.symm
  have h2 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [DivOver.formOrd_formOf_eq_zero hU hE hω, add_zero] at h2
  replace h2 : E.formOrd η = E.ord (Units.mk0 c hc0) := hc ▸ h2
  change E.formOrd η = K.mult w
  rw [h2, h1.mult_eq, hE.ord_eq]

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderBirationalPullback
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BirOrd

theorem formOrd_ratPull_of_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ (n : ℕ) (η : RatForms p n), η ≠ 0 → E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
  intro k _ X Y _ _ p s _ hbij E' E hO n η hη
  set φ := functionFieldMap s with hφdef
  let φe : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective φ hbij
  have hpc : φ.comp (Cartier.constFn p) = Cartier.constFn (s ≫ p) :=
    EtaleKlt.functionFieldMap_comp_constFn p s
  have hcc : (φe.symm : Y.functionField →+* X.functionField).comp (Cartier.constFn (s ≫ p)) =
      Cartier.constFn p := by
    ext a
    rw [← hpc]
    exact φe.symm_apply_apply _

  let Φ' := TopForm.formMap n (φe.symm : Y.functionField →+* X.functionField) hcc
  have hinv : ∀ ξ : RatForms p n, Φ' (EtaleKlt.ratPull p s n ξ) = ξ := by
    intro ξ
    have e0 : (φe.symm : Y.functionField →+* X.functionField).comp φ = RingHom.id _ := by
      ext x
      exact φe.symm_apply_apply x
    refine (TopForm.formMap_formMap φ (φe.symm : Y.functionField →+* X.functionField)
      (RingHom.id _) e0 hpc hcc (RingHom.id_comp _) ξ).trans ?_
    exact TopForm.formMap_of_eq_id _ rfl _ ξ

  let ψ : E.ring →+* E'.ring := φ.restrict E.ring E'.ring fun x hx => (hO x).1 hx
  have hψv : ∀ a, (ψ a : Y.functionField) = φ a := fun _ => rfl
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b h => Subtype.ext (hbij.1 (by simpa [hψv] using congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hbij.2 (y : Y.functionField)
    have hxE : x ∈ E.ring := (hO x).2 (hx ▸ y.2)
    exact ⟨⟨x, hxE⟩, Subtype.ext hx⟩
  let eψ : E.ring ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  let χ : E'.ring →+* E.ring := eψ.symm
  have hc : ψ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun hpc a
  have hc' : χ.comp E'.const = E.const := by
    ext a
    rw [← hc]
    exact congrArg Subtype.val (eψ.symm_apply_apply (E.const a))
  have hχv : ∀ y, ((χ y : E.ring) : X.functionField) = φe.symm (y : Y.functionField) := by
    intro y
    obtain ⟨x, rfl⟩ := eψ.surjective y
    have h1 : χ (eψ x) = x := eψ.symm_apply_apply x
    rw [h1]
    exact (φe.symm_apply_apply (x : X.functionField)).symm

  have hord : ∀ g : X.functionFieldˣ, E'.ord (Units.map φ.toMonoidHom g) = E.ord g := by
    intro g
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
    exact EtaleDiv.log_ordFrac_map E.ring E'.ring φ ψ hψv ht (ht.map eψ) g.ne_zero
  have hfe : ∀ ω : Forms E.const n, IsFreeGen E.ring ω →
      IsFreeGen E'.ring (TopForm.formMap n ψ hc ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective ψ hψb) hc hω
  have hfe' : ∀ ω : Forms E'.const n, IsFreeGen E'.ring ω →
      IsFreeGen E.ring (TopForm.formMap n χ hc' ω) := fun ω hω =>
    EtaleDiv.isFreeGen_formMap (EtaleDiv.formallyEtale_of_bijective χ eψ.symm.bijective) hc' hω
  have hτ : (E'.ring.subtype.comp ψ).comp E.const = Cartier.constFn (s ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ∀ ω : Forms E.const n,
      EtaleKlt.ratPull p s n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hc ω) := by
    intro ω
    have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ψ := by
      ext x
      rfl
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl hpc hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ψ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hτ' : (E.ring.subtype.comp χ).comp E'.const = Cartier.constFn p := by
    rw [RingHom.comp_assoc, hc']
    rfl
  have key' : ∀ ω : Forms E'.const n,
      Φ' (E'.toRat n ω) = E.toRat n (TopForm.formMap n χ hc' ω) := by
    intro ω
    have e : (φe.symm : Y.functionField →+* X.functionField).comp E'.ring.subtype =
        E.ring.subtype.comp χ := by
      ext y
      exact (hχv y).symm
    have k1 := TopForm.formMap_formMap (D := n) E'.ring.subtype
      (φe.symm : Y.functionField →+* X.functionField) _ e rfl hcc hτ' ω
    have k2 := TopForm.formMap_formMap (D := n) χ E.ring.subtype _ rfl hc' rfl hτ' ω
    exact k1.trans k2.symm
  have fwd : ∀ a, E.IsFormOrd η a → E'.IsFormOrd (EtaleKlt.ratPull p s n η) a := by
    rintro a ⟨ω, hω, g, hη', hg⟩
    refine ⟨_, hfe ω hω, Units.map φ.toMonoidHom g, ?_, (hord g).trans hg⟩
    rw [hη', map_smulₛₗ, key]
    rfl
  have bwd : ∀ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a → E.IsFormOrd η a := by
    rintro a ⟨ω, hω, f, hη', hf⟩
    let g : X.functionFieldˣ := Units.map (φe.symm : Y.functionField →+* X.functionField).toMonoidHom f
    have hgf : Units.map φ.toMonoidHom g = f := by
      ext
      exact φe.apply_symm_apply (f : Y.functionField)
    refine ⟨_, hfe' ω hω, g, ?_, ?_⟩
    · rw [← hinv η, hη', map_smulₛₗ, key']
      rfl
    · rw [← hord g, hgf, hf]
  have hne : EtaleKlt.ratPull p s n η ≠ 0 := by
    intro h0
    apply hη
    rw [← hinv η, h0, map_zero]
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq hη, (fwd a ha).formOrd_eq hne]
  · have h' : ¬ ∃ a, E'.IsFormOrd (EtaleKlt.ratPull p s n η) a :=
      fun ⟨a, ha⟩ => h ⟨a, bwd a ha⟩
    rw [DivOver.formOrd, DivOver.formOrd, dite_eq_right h, dite_eq_right h']

end GlobalTheory.BirOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem DVR.fractionRing_eq_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  intro V _ _ _ ϖ hϖ y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨n₁, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n₂, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(n₁ : ℤ) - n₂, u₁ * u₂⁻¹, ?_⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact hϖ.ne_zero
  have hu : ∀ u : Vˣ, algebraMap V (FractionRing V) (u : V) ≠ 0 := fun u => by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact u.ne_zero
  have h2 := hu u₂
  have h1 := hu u₁
  have key : algebraMap V (FractionRing V) ((u₂⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u₂ : V))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, key, zpow_sub₀ hϖ0, zpow_natCast]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
section
set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
end
end

