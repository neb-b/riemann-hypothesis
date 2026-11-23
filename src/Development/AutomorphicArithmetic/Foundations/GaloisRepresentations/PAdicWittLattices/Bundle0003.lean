module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHBasis
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHBasis :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis := by
  classical
  intro k k' _ _ _ J e M N _ _ _ _ ψ hψ I c
  let T : (I →₀ k') ≃+ (J →₀ M) :=
    (Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans
      ((Finsupp.domCongr (Equiv.prodComm I J)).trans
        (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))
  have hTs : ∀ (i : I) (a : k'),
      T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a) := by
    intro i a
    ext j
    simp only [Finsupp.mapRange_apply]
    simp [T, Finsupp.curryAddEquiv]
    have h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j)
        = Finsupp.single i (e.repr a j) := by
      ext i'
      simp only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    rw [h, Finsupp.linearCombination_single]
  have hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m) := by
    intro f
    simp [bcSum]; rfl
  let Φ : (I →₀ k') →ₗ[k'] N := Finsupp.linearCombination k' (fun i => ψ (c i))
  have key : ∀ g, Φ g = bcSum e ψ (T g) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single i a =>
      rw [hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]
      simp only [Φ, Finsupp.linearCombination_single]
      conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  have hΦ : Function.Bijective Φ := by
    have h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T := funext key
    rw [h]
    exact hψ.comp T.bijective
  let E := LinearEquiv.ofBijective Φ hΦ
  refine ⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofRepr]
  simp [E, Φ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHCube
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

section
variable {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
  (e : Module.Basis J k k')

private theorem bcSum_mapRange {M N M' N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [AddCommGroup M'] [Module k M'] [AddCommGroup N'] [Module k' N']
    (ψ : M →ₛₗ[algebraMap k k'] N) (ψ' : M' →ₛₗ[algebraMap k k'] N') (f : M → M') (hf : f 0 = 0)
    (hfa : ∀ a b, f (a + b) = f a + f b) (g : N →ₗ[k'] N') (h : ∀ m, ψ' (f m) = g (ψ m))
    (x : J →₀ M) : bcSum e ψ' (x.mapRange f hf) = g (bcSum e ψ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapRange_add hfa, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | single j m => rw [Finsupp.mapRange_single, bcSum_single, bcSum_single, map_smul, h]

private theorem isBC_pi {T : Type} [Finite T] {M N : T → Type} [∀ t, AddCommGroup (M t)]
    [∀ t, Module k (M t)] [∀ t, AddCommGroup (N t)] [∀ t, Module k' (N t)]
    (ψ : ∀ t, M t →ₛₗ[algebraMap k k'] N t)
    (Ψ : (∀ t, M t) →ₛₗ[algebraMap k k'] (∀ t, N t)) (hΨ : ∀ x t, Ψ x t = ψ t (x t))
    (h : ∀ t, IsBC e (ψ t)) : IsBC e Ψ := by
  classical
  have := Fintype.ofFinite T
  have key : ∀ (x : J →₀ ∀ t, M t) t,
      bcSum e Ψ x t = bcSum e (ψ t) (x.mapRange (fun m => m t) rfl) := by
    intro x t
    have := bcSum_mapRange e Ψ (ψ t) (fun m => m t) rfl (fun a b => rfl) (LinearMap.proj t)
      (fun m => (hΨ m t).symm) x
    simpa using this.symm
  constructor
  · intro x y hxy
    ext j t
    have h1 : x.mapRange (fun m => m t) rfl = y.mapRange (fun m => m t) rfl := by
      apply (h t).1
      rw [← key, ← key, hxy]
    have := congrArg (fun z => z j) h1
    simpa using this
  · intro y
    choose x hx using fun t => (h t).2 (y t)
    refine ⟨∑ t, (x t).mapRange (Pi.single t) (Pi.single_zero t), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hs : ∀ t, bcSum e Ψ ((x t).mapRange (Pi.single t) (Pi.single_zero t)) = Pi.single t (y t) := by
      intro t
      rw [bcSum_mapRange e (ψ t) Ψ (Pi.single t) (Pi.single_zero t)
        (fun a b => Pi.single_add t a b) (LinearMap.single k' N t) ?_ (x t)]
      · simp [hx]
      · intro m
        funext s
        rw [hΨ]
        by_cases hst : s = t
        · subst hst
          simp
        · simp [Pi.single_eq_of_ne hst]
    simp only [hs]
    exact Finset.univ_sum_single y

end

theorem UpperTheory.Gal.G3.jHCube :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube := by
  unfold P_cube
  intro k k' _ _ _ J e ι _ _ A B ψ hψ
  classical
  have := Fintype.ofFinite ι
  have hT : ∀ q, IsBC e (ψ.term (q + 1)) := by
    intro q
    exact isBC_pi e (fun s : {s : Finset ι // s.card = q + 1} => ψ.app s.1) (ψ.term (q + 1))
      (fun x s => rfl) (fun s => hψ s.1 (Finset.card_pos.1 (by rw [s.2]; omega)))
  have hd : ∀ q (w : J →₀ A.Term q), bcSum e (ψ.term (q + 1)) (w.mapRange (A.d q) (map_zero _))
      = B.d q (bcSum e (ψ.term q) w) := fun q w =>
    bcSum_mapRange e (ψ.term q) (ψ.term (q + 1)) (A.d q) (map_zero _) (fun a b => map_add _ a b)
      (B.d q) (fun m => ψ.term_d q m) w
  have hz : ∀ q (x : J →₀ (A.d q).ker), ((bcSum e (ψ.cocycle q) x : (B.d q).ker) : B.Term q)
      = bcSum e (ψ.term q) (x.mapRange Subtype.val rfl) := fun q x =>
    (bcSum_mapRange e (ψ.cocycle q) (ψ.term q) Subtype.val rfl (fun a b => rfl)
      (B.d q).ker.subtype (fun m => rfl) x).symm
  have hZ : ∀ q, IsBC e (ψ.cocycle (q + 1)) := by
    intro q
    constructor
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      rw [hz, hz] at h1
      have h2 := (hT q).1 h1
      refine Finsupp.ext fun j => Subtype.ext ?_
      simpa using congrArg (fun w => w j) h2
    · intro z
      obtain ⟨w, hw⟩ := (hT q).2 (z : B.Term (q + 1))
      have h0 : w.mapRange (A.d (q + 1)) (map_zero _) = 0 := by
        apply (hT (q + 1)).1
        rw [hd, hw, map_zero]
        exact (LinearMap.mem_ker).1 z.2
      have hw0 : ∀ j, A.d (q + 1) (w j) = 0 := fun j => by
        simpa using congrArg (fun v => v j) h0
      let x : J →₀ (A.d (q + 1)).ker :=
        w.mapRange (fun v => if hv : A.d (q + 1) v = 0 then (⟨v, hv⟩ : (A.d (q + 1)).ker) else 0)
          (by simp; rfl)
      have hxw : x.mapRange Subtype.val rfl = w := by
        ext j
        simp [x, hw0 j]
      refine ⟨x, Subtype.ext ?_⟩
      rw [hz, hxw, hw]
  intro p
  have hH : ∀ x : J →₀ (A.d (p + 1)).ker,
      bcSum e (ψ.homology p) (x.mapRange (cechClass A p) (map_zero _))
        = cechClass B p (bcSum e (ψ.cocycle (p + 1)) x) := fun x =>
    bcSum_mapRange e (ψ.cocycle (p + 1)) (ψ.homology p) (cechClass A p) (map_zero _)
      (fun a b => map_add _ a b) (cechClass B p) (fun m => ψ.homology_cechClass p m) x
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero (cechClass A p))
      (cechClass_surjective A p) c
    rw [hH] at hc
    cases p with
    | zero =>
      rw [cechClass_zero_eq_zero_iff] at hc
      have hx : x = 0 := (hZ 0).1 (by rw [hc, map_zero])
      simp [hx]
    | succ q =>
      rw [cechClass_succ_eq_zero_iff] at hc
      obtain ⟨y, hy⟩ := hc
      obtain ⟨w, rfl⟩ := (hT q).2 y
      rw [← hd, hz] at hy
      have h2 := (hT (q + 1)).1 hy
      ext j
      have hj := congrArg (fun v => v j) h2
      simp only [Finsupp.mapRange_apply] at hj
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
      rw [cechClass_succ_eq_zero_iff]
      exact ⟨w j, hj⟩
  · intro h
    obtain ⟨z, rfl⟩ := cechClass_surjective B p h
    obtain ⟨x, rfl⟩ := (hZ p).2 z
    exact ⟨_, hH x⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHEquiv :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv := by
  intro k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ
  let R : (J →₀ M₀) ≃+ (J →₀ M) := Finsupp.mapRange.addEquiv E.toAddEquiv
  have key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hf, hg]
    | single j m =>
      simp only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]
      rw [bcSum_single, bcSum_single, h, map_smul]
      rfl
  have hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R := funext key
  show Function.Bijective ⇑(bcSum e ψ₀)
  rw [hfun]
  exact E'.bijective.comp (hψ.comp R.bijective)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN
open KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory.Gal.G3

private theorem isBC_iff {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [Module k N] [IsScalarTower k k' N] (ψ : M →ₛₗ[algebraMap k k'] N)
    (f : M →ₗ[k] N) (hf : ∀ m, f m = ψ m) : IsBC e ψ ↔ IsBaseChange k' f := by
  classical
  let L : k' ⊗[k] M →ₗ[k] N := TensorProduct.lift
    (((Algebra.linearMap k' (Module.End k' (M →ₗ[k] N))).flip f).restrictScalars k)
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := M) e
  have hL : bcSum e ψ = L.toAddMonoidHom.comp E.symm.toLinearMap.toAddMonoidHom :=
    Finsupp.addHom_ext fun j m ↦ by
      rw [bcSum_single]
      simp [L, E, hf]
  change Function.Bijective (bcSum e ψ) ↔ Function.Bijective L
  rw [hL]
  exact Function.Bijective.of_comp_iff L E.symm.bijective

private theorem isBaseChange_bottom {k k' B B' : Type} [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] {P Q : Type*}
    [AddCommGroup P] [Module B P] [Module k P] [IsScalarTower k B P] [AddCommGroup Q] [Module B' Q]
    [Module B Q] [Module k' Q] [Module k Q] [IsScalarTower B B' Q] [IsScalarTower k' B' Q]
    [IsScalarTower k k' Q] [IsScalarTower k B Q] {u : P →ₗ[B] Q} (hu : IsBaseChange B' u) :
    IsBaseChange k' (u.restrictScalars k) :=
  IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange k k' B B' P).symm ≪≫ₗ hu.equiv.restrictScalars k')
    fun p ↦ by simp

private theorem isBaseChange_map (k k' B B' : Type) [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] :
    IsBaseChange B' (KaehlerDifferential.map k k' B B') := by
  refine IsBaseChange.of_equiv (tensorKaehlerEquiv k k' B B') fun ω ↦ ?_
  have h : ((tensorKaehlerEquiv k k' B B').toLinearMap.restrictScalars B) ∘ₗ
      (TensorProduct.mk B B' Ω[B⁄k] 1) = KaehlerDifferential.map k k' B B' := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    simp [tensorKaehlerEquiv_tmul_D]
  exact LinearMap.congr_fun h ω

theorem jHForms : P_forms := by
  intro k k' _ _ _ J e B B' _ _ _ _ α hα hB j
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := .of_algebraMap_eq fun r ↦ (hα.map_algebraMap r).symm
  haveI : Algebra.IsPushout k k' B B' := ⟨(isBC_iff e (semiSl hα) _ fun _ ↦ rfl).1 hB⟩
  have hone (ω : Ω[B⁄k]) : hα.m1 ω = KaehlerDifferential.map k k' B B' ω := by
    induction ω using ind1 with
    | h b c => rw [hα.oneFormMap_smul_semilinear, hα.m1_D, map_smul, map_D]; rfl
    | h0 => simp
    | ha x y hx hy => simp only [map_add (f := _), hx, hy]
  let pull : Om k B j →ₗ[B] Om k' B' j :=
    { toFun := hα.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ hα.mOm_smul b x }
  have hpull : exteriorPowerMapOver B' j (KaehlerDifferential.map k k' B B') = pull := by
    apply exteriorPower.linearMap_ext
    ext1 v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
    refine Subtype.ext ?_
    change _ = hα.mDR (exteriorPower.ιMulti B j v : DR k B)
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    exact ((hα.mDR_ι (v i)).trans (congrArg ι1 (hone (v i)))).symm
  exact (isBC_iff e (hα.mOm j) _ fun x ↦ LinearMap.congr_fun hpull x).2
    (isBaseChange_bottom (k := k) (k' := k') (B := B) (B' := B')
      (TopForm.isBaseChange_exteriorPower (isBaseChange_map k k' B B') j))

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHFun
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHFun :
    ∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b)) := by
  intro k k' _ _ X X' Y Y' s s' g r r' e f f' _ _ _ _ H U hU hU' hle b
  have hfU : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hUY : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = e ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f' ⁻¹ᵁ (g ⁻¹ᵁ U) := (inf_eq_right.mpr hle).symm
  have hP := (isIso_pushoutSection_iff H (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    le_rfl le_rfl hUY).mp (isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY hU hU' hfU)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hP
  letI iBC : Algebra (Sec s U) (Sec s' (g ⁻¹ᵁ U)) := (appSecS s s' g U).toAlgebra
  letI iBB : Algebra (Sec s U) (Sec r (f ⁻¹ᵁ U)) := secAlg s r f U
  letI iCC : Algebra (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) := secAlg s' r' f' (g ⁻¹ᵁ U)
  letI iBC' : Algebra (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((Sec.res r' hle).toRingHom.comp (appSecS r r' e (f ⁻¹ᵁ U))).toAlgebra
  letI iBX : Algebra (Sec s U) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((algebraMap (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))).comp
      (algebraMap (Sec s U) (Sec s' (g ⁻¹ᵁ U)))).toAlgebra
  haveI t1 : IsScalarTower (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t2 : IsScalarTower (Sec s U) (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun x => (congrArg (fun φ => CommRingCat.Hom.hom φ x) hP.w).symm)
  haveI := sec_finite (s := s) (s' := r) (f := f) hU
  haveI := sec_etale (s := s) (s' := r) (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec r (f ⁻¹ᵁ U))
  haveI := sec_finite (s := s') (s' := r') (f := f') hU'
  haveI := sec_etale (s := s') (s' := r') (f := f') hU'
  haveI := projective_of_etale (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))
  haveI hPo : Algebra.IsPushout (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r (f ⁻¹ᵁ U))
      (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    CommRingCat.isPushout_iff_isPushout.mp hP.flip
  exact (algTrace_of_isPushout (B := Sec s U) (B' := Sec r (f ⁻¹ᵁ U)) (C := Sec s' (g ⁻¹ᵁ U))
    (C' := Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) b).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHOmega
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHOmega :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_forms → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_sections → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega := by
  intro hE hF hS hA k k' _ _ _ J e X X' s s' g h a V hV
  letI := algΓ s
  letI := algΓ s'
  haveI : IsAffineHom g := hA k k' (algebraMap k k') X X' s s' g h
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hForms : IsBC e (formPullS h.w V a) :=
    hF k k' J e _ _ _ (semiHom_appSecS h.w V) (hS k k' J e X X' s s' g h V hV) a
  refine hE k k' J e _ _ _ _ (formPullS h.w V a) (omSecEquiv s a ⟨V, hV⟩).symm
    (omSecEquiv s' a ⟨g ⁻¹ᵁ V, hV'⟩) _ (fun x ↦ ?_) hForms
  obtain ⟨y, rfl⟩ := (omSecEquiv s a ⟨V, hV⟩).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact omegaPullS_toOmega h.w a V y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIsBC
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

private theorem iInf_pre {X X' : Scheme.{0}} (g : X' ⟶ X) {n : ℕ} (U : Fin n → X.Opens)
    (S : Finset (Fin n)) : (⨅ i ∈ S, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨅ i ∈ S, U i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S _ ih
    rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

private theorem pull_isBC (pE : P_equiv) (pC : P_cube) (pA : P_affine) (pV : P_cover)
    (pO : P_omega) (pH : P_cech) {k k' : Type} [Field k] [Field k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) [IsProper s] (a b : ℕ) :
    IsBC e (hodgePullS h.w a b) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨n, U, hc, hU⟩ := pV k X s
  haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h
  have hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  have hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i) := by
    intro S hS
    rw [iInf_pre]
    exact IsAffineHom.isAffine_preimage _ (hU S hS)
  have hcube : IsBC e
      ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b) := by
    apply pC k k' J e (Fin n)
    intro S hS
    have hA : IsAffineOpen (cechOpen ⊤ U S) := by
      rw [cechOpen, top_inf_eq]
      exact hU S hS
    refine pE k k' J e _ _ _ _
      (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S))
      (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_
      (pO k k' J e X X' s s' g h a _ hA)
    intro x
    exact (sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm
  refine pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm
    (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube
  intro x
  obtain ⟨y, rfl⟩ := (cechHEquivCoh k hc hU (Omega s a) b).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y

theorem UpperTheory.Gal.G3.jHBC :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cech → (∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y)) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC := by
  intro pB pE pC pA pV pO pH pT k k' _ _ φ
  refine ⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩
  · intro X X' s s' g h _ a b I c
    letI : Algebra k k' := φ.toAlgebra
    have h₀ : IsPullback g s' s (spMap (algebraMap k k')) := h
    exact pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b)
      (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c
  · intro X X' Y Y' s s' g h r r' e he f hf f' hf' w a b
    exact ⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x,
      fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩
end

