module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => (show _ ∈ H.U i ∧ _ ∈ H.U j from hz).2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesMulVecOfGenericValue
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valF_appLE {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f)
    {U : M.Z.Opens} {V : M'.Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : (V : Set M'.Z).Nonempty) (g : Γ(M.Z, U)) :
    M'.res V hV ((f.appLE U V e).hom g) = φ (valF M.pt U g) := by
  rw [res_apply, ← hf.valF_app ⟨_, e hV.some_mem⟩ g]
  exact (valR_appLE M'.pt f e (M'.top_le_preimage_pt hV) g).trans (valR_comp M'.pt f U g)

theorem crd_mulVec_of_hasVal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  intro o Ω _ _ _ M Ω' _ _ φ N N' a q W H d J _ st σ t u c ha hq hW ht hu htu R _ x w hx
  obtain ⟨k, e, hk, hw⟩ := hx
  have ea : (H.pull a).U k ≤ a ⁻¹ᵁ H.U (k PUnit.unit) := LB.wchart_le H _ k PUnit.unit
  have eq : (H.pull a).U k ≤ q ⁻¹ᵁ W := fun z _ => hW z
  refine ⟨k PUnit.unit, e, le_preimage_comp x a ea hk, fun i => ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hC : (((H.pull a).U k : N'.Z.Opens) : Set N'.Z).Nonempty := ⟨x y, hk (x := y) trivial⟩
  have key : (a.appLE _ _ ea).hom ((st i).f (k PUnit.unit)) =
      ∑ j, (q.appLE _ _ eq).hom (c i j) * (σ j).f k := by
    apply N'.res_injective _ hC
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ha.valF_appLE ea hC, ht i _ ⟨_, ea hC.some_mem⟩, htu]
    simp only [map_mul, hq.valF_appLE eq hC, AlgHom.id_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_apply, hu j k hC, mul_div_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← valR_appLE x a ea hk, key, valR_eq x _ hk, map_sum, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← valR_eq x _ hk, ← valR_eq x _ hk, valR_appLE x q eq hk, hw j, mul_left_comm]

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.CrdMove

theorem stk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem stk_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR_of_field, valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem crd_iff {F : Type} [Field F] {X : Scheme.{0}} {H : LB X} {J : Type} (s : J → H.Sec) (x : Sp F ⟶ X)
    (v : J → F) (z : Sp F) : Crd H s x v ↔ ∃ (l : H.ι) (c : ((Sp F).presheaf.stalk z)ˣ), x z ∈ H.U l ∧
      ∀ j, toStk z (v j) = c.val * gs x z (H.U l) ((s j).f l) := by
  constructor
  · rintro ⟨l, c, hl, hv⟩
    have hz := (top_le_iff_mem x _ z).1 hl
    refine ⟨l, Units.map (toStk z).toMonoidHom c, hz, fun j => ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz]
    rfl
  · rintro ⟨l, c, hz, hv⟩
    obtain ⟨d, hd⟩ := stk_onto z c.val
    have d0 : d ≠ 0 := fun h0 => by
      have : Nontrivial ((Sp F).presheaf.stalk z) := inferInstance
      rw [h0, map_zero] at hd
      exact Units.ne_zero _ hd.symm
    refine ⟨l, Units.mk0 d d0, (top_le_iff_mem x _ z).2 hz, fun j => (toStk z).injective ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz, Units.val_mk0, hd]

theorem crd_move {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {L₀ : LB G.left} {L₁ : LB A.left} (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) {n : ℤ} {I : Type}
    (t : I → LB.Sec (LPow A L₁ n T)) (s : I → LB.Sec (LPow G L₀ n T₀))
    (h : ∀ i, ThetaPtMove.SecRel hp τ hτ w (t i) (s i)) {F : Type} [Field F] (r : Sp F ⟶ (T ⊗ A).left) (v : I → F)
    (hv : Crd (LPow A L₁ n T) t r v) : Crd (LPow G L₀ n T₀) s (r ≫ ThetaPtMove.psi hp τ hτ) v := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨l, c, hl, hc⟩ := (crd_iff t r v z).1 hv
  obtain ⟨J, hJ, -⟩ := exists_good L₀ hL₀ z (K := Empty) (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim)
  obtain ⟨J', hJ', e⟩ := exists_good L₁ hL₁ z (fun _ : Fin 1 => r ≫ (snd T A).left) l
    (fun a b _ => congrArg l (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hl k)
  obtain ⟨d, hd⟩ : ∃ d : ((Sp F).presheaf.stalk z)ˣ, ∀ j,
      VVRank.sv G (s j) (r ≫ ThetaPtMove.psi hp τ hτ) z J = d.val * VVRank.sv A (t j) r z J' :=
    ⟨_, fun j => h j _ r z J J' hJ hJ'⟩
  refine (crd_iff s _ v z).2 ⟨fun _ => J ((r ≫ ThetaPtMove.psi hp τ hτ) ≫ (snd T₀ G).left),
    c * d⁻¹,
    hJ.mem (fun _ : Fin 1 => (snd T₀ G).left) _, fun j => ?_⟩
  have q := hd j
  have q' := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) (t j) r z J' l e
  refine (hc j).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  refine congrArg (c.val * ·) ?_
  rw [Units.eq_inv_mul_iff_mul_eq]
  exact (congrArg (_ * ·) q'.symm).trans q.symm

theorem crd_of_moved : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w _ t ht a v hv
  refine ⟨_, ?_, crd_move u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀)
    (base_eq u) ρ.P.isLB u.A.isLB w t ρ.s ht _ v hv⟩
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) (ThetaPtMove.ptSecT_snd _)).trans ?_)
  exact Category.assoc _ _ _

end GlobalTheory.ZH.CrdMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_point_of_inter {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (i : V →+* K) (j : V →+* O) (k : K →+* C) (l : O →+* C) (hi : Function.Injective i) (hl : Function.Injective l)
    (hc : ∀ v, l (j v) = k (i v)) (hint : ∀ (a : K) (c : O), k a = l c → ∃ v, i v = a)
    {X : Scheme.{0}} (x : Sp K ⟶ X) (b : Sp O ⟶ X) (h : spMap k ≫ x = spMap l ≫ b) :
    ∃ y : Sp V ⟶ X, spMap i ≫ y = x ∧ spMap j ≫ y = b := by
  obtain ⟨U, hU, hb, -⟩ := exists_isAffineOpen_le b (le_preimage_top b)
  have hlb : ⊤ ≤ (spMap l ≫ b) ⁻¹ᵁ U := le_preimage_comp _ b hb (le_preimage_top _)
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ (spMap k ≫ x) ⁻¹ᵁ U := h ▸ hlb
    intro w _
    rw [Subsingleton.elim w (spMap k (IsLocalRing.closedPoint C))]
    exact h1 (x := IsLocalRing.closedPoint C) trivial
  have hv : ∀ f, k ((valMap x U hx).hom f) = l ((valMap b U hb).hom f) := fun f => by
    rw [← valR_eq, ← valR_eq, ← valR_spMap_comp k x U hx, ← valR_spMap_comp l b U hb, h]
  choose g hg using fun f => hint _ _ (hv f)
  let ψ : Γ(X, U) →+* V :=
    { toFun := g
      map_one' := hi (by simp only [hg, map_one])
      map_mul' := fun a c => hi (by simp only [hg, map_mul])
      map_zero' := hi (by simp only [hg, map_zero])
      map_add' := fun a c => hi (by simp only [hg, map_add (f := _)]) }
  have e1 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom i = valMap x U hx := by
    ext f
    exact hg f
  have e2 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom j = valMap b U hb := by
    ext f
    exact hl ((hc _).trans ((congrArg k (hg f)).trans (hv f)))
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e1, specMap_valMap_fromSpec]
  · rw [← Category.assoc, ← Spec.map_comp, e2, specMap_valMap_fromSpec]

theorem pushHom_inj_of_cartesian {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := fun a b e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))

theorem torsion_integral_descends : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u jV hj b hb
  haveI := u.U.gen_hom
  let k : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  have hsq : gPt p ≫ spMap jV = spMap k ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => spMap φ) (RingHom.ext hj)
  have hbw : b.left ≫ u.G.hom = spMap jV := Over.w b
  let T : Over (Sp (FractionRing u.V)) := Over.mk (spMap k)
  let wl : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (gPt p ≫ b.left) (spMap k) (by rw [Category.assoc, hbw, hsq])
  have w1 : wl ≫ pullback.fst _ _ = gPt p ≫ b.left := pullback.lift_fst _ _ _
  have w2 : wl ≫ pullback.snd _ _ = spMap k := pullback.lift_snd _ _ _
  let w : T ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk wl w2
  let W : Over.mk (T.hom ≫ jK u.V) ⟶ Over.mk (spMap jV) := Over.homMk (gPt p) hsq
  have hp := isGrpPullback_pullback u.G (jK u.V)
  have e0 : pushHom hp T w = preHom W b := Over.OverMorphism.ext w1
  have hw : w ^ (S.r * S.N) = 1 := pushHom_inj_of_cartesian hp T (by
    rw [map_pow, e0, ← map_pow, hb, map_one, map_one])
  have hw' : (w ≫ u.U.gen.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (T.hom ≫ spMap u.yK) (pushHom u.cart T (w ≫ u.U.gen.hom))
    (by rw [← map_pow, hw', map_one])
  have ha' : (spMap k ≫ spMap u.yK) ≫ (ρ.pt a).left = (wl ≫ u.U.gen.hom.left) ≫ u.φ :=
    congrArg (fun z => z.left) ha
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hg : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd _ _ := Over.w u.U.gen.hom
  have hg' : u.U.gen.inv.left ≫ pullback.snd _ _ = u.A.A.hom := Over.w u.U.gen.inv
  have hih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.inv_hom_id
  have hhi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.hom_inv_id
  obtain ⟨x', x1, x2⟩ : ∃ x' : Sp (FractionRing u.V) ⟶ u.A.A.left,
      x' ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ x' ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa, Category.id_comp]; exact Category.comp_id _), u.cart.1.lift_fst _ _ _,
      u.cart.1.lift_snd _ _ _⟩
  have hx' : spMap k ≫ x' = wl ≫ u.U.gen.hom.left := by
    refine u.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, x1, ← Category.assoc]
      exact ha'
    · rw [Category.assoc, x2, Category.comp_id, Category.assoc]
      exact ((congrArg (wl ≫ ·) hg).trans w2).symm
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) := x' ≫ u.U.gen.inv.left
  have hx : spMap k ≫ x = wl := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.U.gen.inv.left) hx').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (wl ≫ ·) hhi).trans (Category.comp_id _))
  have hxs : x ≫ pullback.snd _ _ = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hg').trans x2)
  obtain ⟨hV, h1, h2⟩ := exists_point_of_inter (algebraMap u.V (FractionRing u.V)) jV k (OO p).subtype
    (IsFractionRing.injective _ _) Subtype.val_injective hj
    (fun a c e => (u.norm_le a).1 ((mem_OO_iff _).1 (by
      have e' : algebraMap _ (PadicAlgCl p) a = c := e
      rw [e']; exact c.2)))
    (x ≫ pullback.fst _ _) b.left (by rw [← Category.assoc, hx, w1])
  refine ⟨a, hV, x, ⟨?_, h1.symm, hxs, ?_⟩, h2⟩
  · rw [← Spec.map_preimage (hV ≫ u.G.hom), ← Spec.map_id]
    congr 1
    have h3 : Spec.preimage (hV ≫ u.G.hom) ≫ CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) =
        CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
      refine (congrArg (· ≫ u.G.hom) h1).trans ?_
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, Category.id_comp]
    ext v
    exact IsFractionRing.injective u.V (FractionRing u.V) (congrArg (fun φ => φ.hom v) h3)
  · refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (x' ≫ ·) ?_) x1)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) hih).trans (Category.id_comp _))

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}
  {J : Type} {σ : J → H.Sec} {t : J → Ω}

theorem mem_nonzeroLocus_iff_div (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hg : ∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) (i : J) (z : M.Z) :
    z ∈ Out.nonzeroLocus (σ i) ↔ M.Div t i z := by
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
    obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
    have e := hv i l ⟨z, hzl⟩
    dsimp only at h0 h1
    rw [e] at h0 h1
    have hi : t i ≠ 0 := fun h => h0 (by rw [h, zero_div])
    refine ⟨hi, fun j => ?_⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (t i / d l)⁻¹ = t j / t i := by field_simp
    rwa [e'] at h3
  · intro hz
    have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i', hi', h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 ((isUnit_O_iff _).2 ?_)⟩
    dsimp only
    rw [hv i l ⟨z, hzl⟩]
    refine ⟨div_ne_zero hz.1 (hd.ne l), ?_⟩
    have h3 := mul_mem h1 (hz.2 i')
    have hi := hz.1
    have e' : d l / t i' * (t i' / t i) = (t i / d l)⁻¹ := by field_simp
    rwa [e'] at h3

theorem immBy_of_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  intro o Ω _ _ _ M H d J σ t k _ p ψ hH hd hv hg hp hU
  have key := mem_nonzeroLocus_iff_div hH hd hv hg
  refine ⟨top_unique fun z _ => ?_, fun i _ => ?_⟩
  · have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i, hi, h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨trivial, (key i z).2 ⟨hi, fun j => ?_⟩⟩⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (d l / t i) = t j / t i := by field_simp
    rwa [e'] at h3
  · have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
      have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
      subst this
      infer_instance
    have key' := key i
    generalize Out.nonzeroLocus (σ i) = W at key' ⊢
    by_cases hi : t i = 0
    · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
      subst hW
      refine ⟨isAffineOpen_bot _, fun _ => 0, fun j l => ?_,
        top_unique fun f _ => Subsingleton.elim 0 f ▸ zero_mem _⟩
      have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
      exact Subsingleton.elim _ _
    · obtain ⟨U, hUa, hUe, hR⟩ := hU i hi
      have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
      subst hWU
      have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
      have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
        (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
      choose r hr using hr
      refine ⟨hUa, r, fun j l => ?_, ?_⟩
      · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
        · have hl' : (H.U l : Set M.Z).Nonempty :=
            Set.Nonempty.mono (show (W ⊓ H.U l : M.Z.Opens) ≤ H.U l from inf_le_right) hl
          apply M.res_injective _ hl
          rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
            hv j l hl', hv i l hl', hr]
          have hdl := hd.ne l
          field_simp
        · have := hempty _ hl
          exact Subsingleton.elim _ _
      · refine top_unique fun f _ => ?_
        have h1 := hR _ ((mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩)
        have e : (Set.range ψ ∪ Set.range fun j => t j / t i) =
            M.res W hne '' (Set.range (constFn p W) ∪ Set.range r) := by
          rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
          congr 2
          · funext a
            exact ((M.res_apply W hne _).trans
              (valR_constFn_of_over p ψ M.pt hp W (M.top_le_preimage_pt hne) a)).symm
          · funext j
            exact ((M.res_apply W hne _).trans (hr j)).symm
        rw [e, ← RingHom.map_closure] at h1
        obtain ⟨g, hg1, hg2⟩ := h1
        have : g = f := M.res_injective W hne (hg2.trans (M.res_apply W hne f).symm)
        exact this ▸ hg1

end GlobalTheory.ZH.RatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Mod.integral_of_weight_zero_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  intro p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi
  obtain ⟨ν, hν, hc⟩ := m.ser a ha w hw
  apply hc
  let e : m.Φ.E.X ≃ₗ[ℤ] X := m.xe.toIntLinearEquiv
  have : Module.Free ℤ X := Module.Free.of_equiv e
  have : Module.Finite ℤ X := Module.Finite.equiv e
  have hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x := by
    intro x
    rw [QuadraticMap.comp_apply]
    exact congrArg q (m.xe.apply_symm_apply x)
  refine _root_.GlobalTheory.ZH.ValLat.main X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi
  · have h := m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)
    exact h.congr hq
  · exact e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)
  · intro i n
    have h := m.good.short i (m.xe.symm n)
    rw [← map_nsmul, ← map_add (f := _), hq, hq] at h
    exact h

end GlobalTheory.ZH
end

