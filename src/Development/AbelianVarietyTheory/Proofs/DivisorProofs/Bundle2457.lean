module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalHomCompletedStalkToDvrOverTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitLocal

theorem comap_maximalIdeal_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (ϖ : V) (hϖ : Irreducible (h ϖ)) :
    Ideal.comap h (maximalIdeal V') = maximalIdeal V := by
  have hne : Ideal.comap h (maximalIdeal V') ≠ ⊥ := by
    intro h0
    have : ϖ ∈ Ideal.comap h (maximalIdeal V') := hϖ.not_isUnit
    rw [h0, Ideal.mem_bot] at this
    exact hϖ.ne_zero (by rw [this, map_zero])
  haveI : (Ideal.comap h (maximalIdeal V')).IsPrime := Ideal.comap_isPrime _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

theorem maximalIdeal_le_map {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R]
    [IsLocalRing R] (j : O →+* R) (hj : IsCpl j) : maximalIdeal R ≤ Ideal.map j (maximalIdeal O) := by
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal O) O) := AdicCompletion.isLocalRing_of_fg fg
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  intro r hr
  have h1 : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro hu
    have := hu.map e
    rw [RingEquiv.apply_symm_apply] at this
    exact hr this
  rw [hm] at h1
  have h2 := Ideal.mem_map_of_mem (e : AdicCompletion (maximalIdeal O) O →+* R) h1
  rw [Ideal.map_map] at h2
  have h3 : (e : AdicCompletion (maximalIdeal O) O →+* R).comp (algebraMap O _) = j := by
    first | exact he | exact RingHom.ext he | exact he.symm
  rw [h3] at h2
  simpa using h2

end GlobalTheory.Poinc.TraitLocal

theorem GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  intro o' Ω _ _ _ hA M x R _ _ j hj V _ _ _ ϖ V' _ _ _ h g' ξ hϖ hξ hsq
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have h1 : spMap h (closedPoint V') = closedPoint V :=
    PrimeSpectrum.ext (GlobalTheory.Poinc.TraitLocal.comap_maximalIdeal_of_irreducible h ϖ hϖ)
  have h2 : (spMap h ≫ ξ) (closedPoint V') = x :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ h1).trans hξ)
  rw [← hsq] at h2
  have h3 : M.Z.fromSpecStalk x (spMap j (spMap g' (closedPoint V'))) =
      M.Z.fromSpecStalk x (closedPoint (M.Z.presheaf.stalk x)) :=
    h2.trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 := (M.Z.fromSpecStalk x).isEmbedding.injective h3
  have h5 : Ideal.comap j (Ideal.comap g' (maximalIdeal V')) = maximalIdeal (M.Z.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal h4
  have h6 : maximalIdeal R ≤ Ideal.comap g' (maximalIdeal V') :=
    (GlobalTheory.Poinc.TraitLocal.maximalIdeal_le_map j hj).trans (Ideal.map_le_iff_le_comap.2 h5.ge)
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  exact h6 (show r ∈ maximalIdeal R from hn) hr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isLocallyNoetherian_of_smooth_over_modif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  intro R _ _ _ M G hG
  haveI : IsLocallyNoetherian (Sp R) := inferInstance
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI := hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomSectionOfProdTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory

theorem isMonHom_section_of_prod_trivial :
    ∀ (S : Scheme.{0}) (B B₁ B₂ : Over S) [GrpObj B] [GrpObj B₁] [GrpObj B₂] (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (i₁ : B₁ ⟶ B), IsMonHom p₁ → IsMonHom p₂ → IsIso (lift p₁ p₂) → i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[B₂] → IsMonHom i₁ := by
  intro S B B₁ B₂ _ _ _ p₁ p₂ i₁ h₁ h₂ hiso hi₁ hi₂
  have key : ∀ {X : Over S} (f g : X ⟶ B), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g := by
    intro X f g e₁ e₂
    rw [← cancel_mono (lift p₁ p₂)]
    ext <;> simp [e₁, e₂]
  constructor
  · apply key
    · simp [hi₁]
    · simp only [Category.assoc, hi₂, IsMonHom.one_hom]
  · apply key
    · simp only [Category.assoc, hi₁, IsMonHom.mul_hom, Category.comp_id]
      rw [tensorHom_comp_tensorHom_assoc, hi₁, tensorHom_id, id_whiskerRight, Category.id_comp]
    · simp only [Category.assoc, hi₂, IsMonHom.mul_hom]
      rw [tensorHom_comp_tensorHom_assoc, hi₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv sabT sabM)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.FlagMod GlobalTheory.LocM GlobalTheory.NefCurveTest
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.NefStep

section Span

variable {X : Scheme.{0}} {F : X.Modules} {J : Type} {T : J → X.Opens} {r : ℕ}
  (w : ∀ j, Fin r → Γ(F, T j)) (l : ∀ j, Fin r → Γ(VB.dual F, T j))

def spanSub : Sub F where
  sec V :=
    { carrier := {s | ∀ j (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j),
        resM F h₁ s = ∑ a, dualApp (l j a) h₂ (resM F h₁ s) • resM F h₂ (w j a)}
      add_mem' := fun hs ht j W h₁ h₂ => by
        simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
        rw [← hs j W h₁ h₂, ← ht j W h₁ h₂]
      zero_mem' := fun j W h₁ h₂ => by simp
      smul_mem' := fun a s hs j W h₁ h₂ => by
        simp only [resM_smul, map_smul, smul_assoc, ← Finset.smul_sum]
        rw [← hs j W h₁ h₂] }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine Twist.sec_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, resM_smul, ← dualApp_resM, resM_resM] at this ⊢
    exact this

theorem exists_sub_det {L : LB X} (hL : L.IsLB) (w : ∀ j, Fin r → Γ(F, L.U j)) (l : ∀ j, Fin r → Γ(VB.dual F, L.U j))
    (hl : ∀ j a b, dualApp (l j a) le_rfl (w j b) = if a = b then 1 else 0)
    (B : ∀ j j', Matrix (Fin r) (Fin r) Γ(X, L.U j ⊓ L.U j'))
    (hB : ∀ j j' b, resM F inf_le_right (w j' b) = ∑ a, B j j' a b • resM F inf_le_left (w j a))
    (hg : ∀ j j', (L.g j j').val = (B j j').det) :
    ∃ (W : X.Modules) (i : W ⟶ F), Mono i ∧ IsVB W r ∧ LBIso L (det W r) := by
  have hl' (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) (a) :
      dualApp (l j a) h (∑ b, c b • resM F h (w j b)) = c a := by
    have e (b) : dualApp (l j a) h (resM F h (w j b)) = if a = b then 1 else 0 := by
      rw [dualApp_resM (l j a) le_rfl h, hl]; split_ifs <;> simp
    simp [e]
  let N := spanSub w l
  have hm (j) (b) : w j b ∈ N.sec (L.U j) := fun j' V h₁ h₂ => by
    have e := congrArg (resM F (le_inf h₂ h₁)) (hB j' j b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, resM_smul, resM_resM] at e
    rw [e]
    simp only [hl']
  have hi (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) :
      N.incl.app V (∑ b, c b • resM _ h (N.mkSec _ (hm j b))) = ∑ b, c b • resM F h (w j b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec]
  have he (j) : IsFrame fun b => N.mkSec _ (hm j b) := isFrame_iff.2 fun V h => by
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc a => ?_, fun s _ =>
      (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun a => dualApp (l j a) h (resM F le_rfl (N.incl.app V s)),
        N.incl_app_injective V ((hi j h _).trans ?_)⟩⟩
    · rw [← hl' j h c a, ← hi, hc, map_zero, map_zero]
    · exact (N.incl_app_mem s j V le_rfl h).symm.trans (resM_self _ _)
  refine ⟨N.toMod, N.incl, inferInstance, lbIso_det_of_frames hL _ he fun j j' => Units.ext ?_⟩
  rw [hg, IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  have e : resM _ inf_le_right (N.mkSec _ (hm j' b)) =
      ∑ a, B j j' a b • (he j).basis (inf_le_left : L.U j ⊓ L.U j' ≤ _) a := by
    simp only [IsFrame.basis_apply]
    refine N.incl_app_injective _ (Eq.trans ?_ (hi j _ _).symm)
    rw [app_resM, Sub.incl_app_mkSec, hB]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]

end Span

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)


open Classical in
theorem LL_stepEx_g_inv (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) (k k' : F.J) :
    ((show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL (stepEx σ n)).g k k')⁻¹).val =
      ∏ a : Fin n, F.B k k' σ (a.castLE hn) (a.castLE hn) := by
  have e : (∏ ix, F.T k k' ix ^ (-stepEx σ n ix))⁻¹ = ∏ a : Fin n, F.T k k' (some ⟨σ, a.castLE hn⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun a : Fin n => (some ⟨σ, a.castLE hn⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun a _ => ?_).symm
    · simpa using h
    · rcases ix with _ | ⟨σ', i⟩
      · simp [stepEx]
      · have : ¬ (σ' = σ ∧ (i : ℕ) < n) := by
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, by simp, rfl⟩
        simp [stepEx, this]
    · simp [stepEx]
  refine (congrArg Units.val e).trans ?_
  rw [Units.coe_prod]
  rfl

theorem left_vecAt {S S' : Type} [CommRing S] [CommRing S'] (k : F.J) (φ : S →+* S') {z : Sp S ⟶ Z} {z' : Sp S' ⟶ Z}
    (e : spMap φ ≫ z = z') (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z' hz' rfl σ a)).left = spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (F.vecAt k z hz rfl σ a)).left := by
  subst e
  rw [← F.tanPull_vecAt k φ z hz hz' rfl rfl (Category.assoc _ _ _).symm, tanPull_left]

theorem exists_step_sub {C : Scheme.{0}} [C.IsSeparated] [PreconnectedSpace C] (g : C ⟶ Z) {t : SAB H C}
    (m : SABMap t Y.t (g ≫ π)) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (i : W ⟶ Lie t.G), Mono i ∧ IsVB W n ∧
      LBIso (CechPic.dual ((F.LL (stepEx σ n)).pull g)) (det W n) := by
  have := t.semi
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv m
  obtain ⟨d, -, hd⟩ := exists_isVB_of_isSemiAbelian t.G
  have := hd.isQuasicoherent
  let J := {q : C.Opens × F.J // CoordOpen t q.1 ∧ q.1 ≤ g ⁻¹ᵁ F.U q.2}
  have hin {T : C.Opens} (hT : IsAffineOpen T) {U : Z.Opens} (h : T ≤ g ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ g) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := Opens.mem_iSup.1 (F.cover.ge (Set.mem_univ (g x)))
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen t (V := g ⁻¹ᵁ F.U q) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  let M := CechPic.dual ((F.LL (stepEx σ n)).pull g)
  have hM : M.IsLB := isLB_dual (LB.isLB_pull (F.isLB_LL _) g)
  have hle (j : J) : j.1.1 ≤ M.U fun _ => j.1.2 := j.2.2.trans (GlobalTheory.LB.pull_U (L := F.LL _) g fun _ => j.1.2).ge
  have hL := TriangularFrames.isLB_refine hc hM (fun j : J => fun _ => j.1.2) hle
  let ψ (j : J) := Ψ _ j.2.1 ((affPt j.2.1.1 ≫ g) ≫ π) (Category.assoc _ _ _).symm
  let b (j : J) := (lieBasis (F.M j.1.2).toMChart _ (F.inM (hin j.2.1.1 j.2.2) rfl)).map (ψ j)
  have hb (j : J) : IsFrame (b j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  choose p hp using fun j : J => F.uAt_split j.1.2 _ (hin j.2.1.1 j.2.2) σ
  have hT (j j' : J) : CoordOpen t (j.1.1 ⊓ j'.1.1) := j.2.1.mono (j.2.1.1.inf j'.2.1.1) inf_le_left
  have hh (j j' : J) := hin (hT j j').1 ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
  have hres (j : J) {T : C.Opens} (hT : CoordOpen t T) (h : T ≤ j.1.1) (a : Fin (Dw.mult σ)) :
      resM (Lie t.G) h (ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ a)) =
        Ψ T hT _ (Category.assoc _ _ _).symm (F.vecAt j.1.2 _ (hin hT.1 (h.trans j.2.2)) rfl σ a) := by
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (left_vecAt F _ _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  let w (j : J) (a : Fin n) : Γ(Lie t.G, j.1.1) := ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ (a.castLE hn))
  let f (j : J) (a : Fin n) : Γ(VB.dual (Lie t.G), j.1.1) := ∑ s, p j (a.castLE hn) s • (hb j).coord s
  let B (j j' : J) : Matrix (Fin n) (Fin n) Γ(C, j.1.1 ⊓ j'.1.1) :=
    ((F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j'))).submatrix (Fin.castLE hn) (Fin.castLE hn)
  have h₁ (j : J) (a a' : Fin n) : dualApp (f j a) le_rfl (w j a') = if a = a' then 1 else 0 := by
    have e := congrFun (congrFun (hp j) (a.castLE hn)) (a'.castLE hn)
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Fin.castLE_inj] at e
    rw [← e, dualApp_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e' : w j a' = ∑ s, F.uAt j.1.2 _ (hin j.2.1.1 j.2.2) σ s (a'.castLE hn) • (hb j).basis le_rfl s := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, Frames.vecAt, vec_apply, map_sum, map_smul, IsFrame.basis_apply, resM_self, b,
        Module.Basis.map_apply]
    rw [dualApp_smul, LinearMap.smul_apply, IsFrame.dualApp_coord, e', Module.Basis.repr_sum_self, GlobalTheory.LB.resG_self,
      smul_eq_mul]
  have h₂ (j j' : J) (a : Fin n) : resM (Lie t.G) (inf_le_right : j.1.1 ⊓ j'.1.1 ≤ _) (w j' a) =
      ∑ s, B j j' s a • resM (Lie t.G) inf_le_left (w j s) := by
    refine (hres j' (hT j j') inf_le_right _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [F.vecAt_eq_sum j.1.2 j'.1.2 _ (hin (hT j j').1 (inf_le_left.trans j.2.2)) _ (hh j j'), map_sum]
    refine (Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn (fun _ _ => Finset.mem_univ _)
      (fun s _ h => ?_) fun s _ => ?_).symm
    · have hs : a.castLE hn < s := lt_of_not_ge fun h' => h ⟨⟨s, lt_of_le_of_lt h' a.2⟩, by simp, rfl⟩
      have h0 : (F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j')) s (a.castLE hn) = 0 := F.B_map_tri _ _ σ _ hs
      rw [h0, zero_smul, map_zero]
    · rw [map_smul, ← hres j (hT j j') inf_le_left]
      rfl
  have h₃ (j j' : J) : resG C (inf_le_inf (hle j) (hle j')) (M.g (fun _ => j.1.2) fun _ => j'.1.2).val =
      (B j j').det := by
    have ht : (B j j').BlockTriangular id := fun s s' h =>
      F.B_map_tri j.1.2 j'.1.2 σ (ev _ _ (hh j j')) (i := s.castLE hn) (j := s'.castLE hn) h
    rw [Matrix.det_of_upperTriangular ht]
    simp only [B, Matrix.submatrix_apply, Matrix.map_apply, ← map_prod]
    rw [← LL_stepEx_g_inv F σ hn]
    refine left_inv_eq_right_inv (a := ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val) ?_
      ((map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _)))
    have e : ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val = resG C (inf_le_inf (hle j) (hle j'))
        (((F.LL (stepEx σ n)).pull g).g (fun _ => j.1.2) fun _ => j'.1.2).val := by
      refine Eq.trans ?_ (GlobalTheory.LB.resG_pull_g (L := F.LL _) g _ _ _).symm
      refine (ev_appLE (affPt (hT j j').1) g ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
        (le_preimage_affPt _) _ _).symm.trans ?_
      exact congr($(ev_tau_self (hT j j').1 _) _)
    refine (congrArg (_ * ·) e).trans ((map_mul _ _ _).symm.trans ?_)
    exact (congrArg _ (Units.inv_mul _)).trans (map_one _)
  obtain ⟨W, i, hi, hW, e⟩ := exists_sub_det (F := Lie t.G) hL w f h₁ B h₂ h₃
  exact ⟨W, i, hi, hW, (cls_eq_iff hM hW.isLB_det).1 (((cls_eq_iff hL hM).2
    (TriangularFrames.lbIso_refine hM _ hle)).symm.trans ((cls_eq_iff hL hW.isLB_det).2 e))⟩

theorem curveTest_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] (σ : E →+* ℂ)
    {n : ℕ} (hn : n ≤ Dw.mult σ) : CurveTest K (F.LL (stepEx σ n)) := fun C _ hs hp hc g => by
  have := LieSemineg.isIntegral_curve hs hc
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : C.IsSeparated := ⟨by rw [← terminal.comp_from (strHom K C)]; infer_instance⟩
  obtain ⟨W, i, _, hW, e⟩ := exists_step_sub F g (sabM Out.proved_CubePullSt (g ≫ π) Y.t) σ hn
  have := (sabT Out.proved_CubePullSt (g ≫ π) Y.t).semi
  have hM := LB.isLB_pull (F.isLB_LL (stepEx σ n)) g
  refine (h.dual_det_nonneg hs hp hc _ hW i).trans_eq (interNum_congr_cls K _ (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hM) fun j => ?_)
  fin_cases j
  change cls _ (isLB_dual hW.isLB_det) = cls _ hM
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff (isLB_dual hM) hW.isLB_det).2 e, cls_dual hM, neg_neg]

theorem isNef_pull_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) (k : Type) [Field k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (g : X ⟶ Z) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    IsNef k ((F.LL (stepEx σ n)).pull g) :=
  ((curveTest_LL_stepEx F h (AlgebraicClosure k) σ hn).pull (F.isLB_LL _) g).isNef hN (LB.isLB_pull (F.isLB_LL _) g)

end GlobalTheory.NefStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic

namespace GlobalTheory.Mum.PowData

def AdjCls {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [GrpObj G₀] (c : Pic G.left) (c₀ : Pic G₀.left) (q : G ⟶ G₀)
    (j : G₀ ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G) (z : T ⟶ G₀), lam c x (z ≫ j) = lam c₀ (x ≫ q) z

variable {R : Type} [CommRing R] [IsDomain R]

def PrimVal (D : DegPre R) (f : D.P.A ⟶ D.P.A) (m : D.X → D.X) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ ∀ y, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (m y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)

theorem isPrimitiveValue_of_ringElement_psiRelation {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X] {o : D.OAct O} {w : O}
    (h : TraceFormTwistIso D o w) : PrimVal D (o.onB.act w) (fun y => w • y) :=
  h.imp fun _ h => ⟨h.1, h.2.2⟩

def Expand (D : DegPre R) {K : Type} [Fintype K] (n : K → ℤ) {T : Over (Sp R)} (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb D.P.L (Sum.elim (lamPts x (∏ i, y i ^ n i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
      (Sum.elim Oε (fun k : K × Fin 4 => -(n k.1 * Oε k.2)))),
    κ.IsGen ∧ ∀ (p : TK R ⟶ T) (a : D.X) (b : K → D.X), p ≫ x = toUnit _ ≫ D.c a → (∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) →
      ∀ z J, Good D.P.L z J →
        val (D.tau a (∑ i, n i • b i)) (𝟙 _) z J * val κ p.left z J = ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ n i

def CmpTwo (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A) : Prop :=
  ∃ Γ : LB.Gen (LB.LinComb (JN D D₀)
      (Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
        (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)) (Sum.elim Oε Oinvε)),
    Γ.IsGen ∧ ∀ (χ' : D.X) (χ : D₀.X), D.c χ' = D₀.c χ ≫ j → ∀ u : LB.Gen (CmpLB D D₀ q χ' χ), Nrm u →
      ∀ (T : Over (Sp R)) (x : T ⟶ D.P.A) (z : T.left) (J), Good (JN D D₀) z J →
        val u x.left z J = val Γ (lift x (toUnit T ≫ D₀.c χ)).left z J

def PeriodRel (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (h : D₀.X → D.X) (k : D.X → D₀.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D D₀ q (h χ) χ), Nrm u ∧ ∀ y z J, Good (JN D D₀) z J →
    val (D₀.tau (k y) χ) (𝟙 _) z (rr J) = val (D.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D.c y)) z J

section Points

variable {S : Scheme.{0}} {T T' G G' : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K]

theorem comp_prod_zpow (p : T' ⟶ T) (y : K → (T ⟶ G)) (n : K → ℤ) : p ≫ ∏ i, y i ^ n i = ∏ i, (p ≫ y i) ^ n i := by
  let f : (T ⟶ G) →* (T' ⟶ G) := MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

theorem prod_zpow_comp [GrpObj G'] [IsCommMonObj G'] (y : K → (T ⟶ G)) (n : K → ℤ) (g : G ⟶ G') [IsMonHom g] :
    (∏ i, y i ^ n i) ≫ g = ∏ i, (y i ≫ g) ^ n i := by
  let f : (T ⟶ G) →* (T ⟶ G') := MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

end Points

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

structure IsProdUnif (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (U : UnifPre I D A (G₁ ⊗ G₂))
    (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X)
    (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A) : Prop where
  gen_pr₁ : U.gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom
  gen_pr₂ : U.gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom
  wL : ∃ w : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left), w.IsGen
  q_pr₁ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₁ =
    (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ (U₁.gt e).q
  q_pr₂ : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map p₂ =
    (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ (U₂.gt e).q
  i_pr₁ : ∀ (e : ℕ) (h : D₁.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = t ≫ (U₁.gt e).i
  i_pr₂ : ∀ (e : ℕ) (h : D₂.toPre.X → D.toPre.X), (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
    ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = t ≫ (U₂.gt e).i

variable {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem IsProdUnif.linHom_fst (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₁ : D₁.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₁ y) = y) (h₂ : ∀ y, q₂ (j₁ y) = 0) : LinHom U U₁ p₁ j₁ (fst G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₁ e).symm, fun e => hU.i_pr₁ e j₁ h₁ h₂⟩

theorem IsProdUnif.linHom_snd (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂) (j₂ : D₂.toPre.X →+ D.toPre.X)
    (h₁ : ∀ y, q₁ (j₂ y) = 0) (h₂ : ∀ y, q₂ (j₂ y) = y) : LinHom U U₂ p₂ j₂ (snd G₁ G₂) :=
  ⟨inferInstance, fun e => (hU.q_pr₂ e).symm, fun e => hU.i_pr₂ e j₂ h₁ h₂⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorPropsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_latticeFactor_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s; (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧ Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧ ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  first | exact @GlobalTheory.Mum.tens_factor_latt | exact GlobalTheory.Mum.tens_factor_latt | (intros; apply GlobalTheory.Mum.tens_factor_latt <;> assumption)
end

