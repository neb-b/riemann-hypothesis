module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0018
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0013

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhTorusA
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

open scoped CategoryTheory.Obj

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torFst (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra ZU.{0} X)) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

def chi {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) : Multiplicative X →* Γ(Y, ⊤) :=
  (pb (g ≫ torFst S X)).toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)

theorem chi_apply {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi g x = pb (g ≫ torFst S X) (AddMonoidAlgebra.single x.toAdd 1) := rfl

theorem chi_comp {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi (f ≫ g) x = f.appTop (chi g x) := by
  rw [chi_apply, chi_apply, Category.assoc, pb_comp]

theorem chi_ext {Y : Scheme.{0}} {g h : Y ⟶ (splitTorus S X).left}
    (w : g ≫ (splitTorus S X).hom = h ≫ (splitTorus S X).hom) (e : ∀ x, chi g x = chi h x) : g = h := by
  refine pullback.hom_ext (f := (splitTorusAff ZU X).hom) (g := toZ S) ?_ w
  refine pb_ext (j := g ≫ torFst S X) (j' := h ≫ torFst S X) (RingHom.congr_fun ?_)
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun m => e (Multiplicative.ofAdd m)
  have e1 : ∀ k : Y ⟶ (splitTorus S X).left, pb (k ≫ torFst S X) (AddMonoidAlgebra.single 0 r) = pb (toZ Y) r := by
    intro k
    refine (pb_spec (k ≫ torFst S X) (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)) r).symm.trans ?_
    congr 2
    exact specULiftZIsTerminal.hom_ext _ _
  rw [e1, e1]

theorem exists_chi (Y : Over S) (c : Multiplicative X →* Γ(Y.left, ⊤)) :
    ∃ g : Y ⟶ splitTorus S X, ∀ x, chi g.left x = c x := by
  obtain ⟨j, hj⟩ := exists_pb (AddMonoidAlgebra.liftNCRingHom (k := ZU.{0}) (pb (toZ Y.left)) c
    fun _ _ => Commute.all _ _)
  refine ⟨Over.homMk (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), fun x => ?_⟩
  have e : (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) ≫ torFst S X = j := pullback.lift_fst _ _ _
  refine (congrArg (fun k => pb k (AddMonoidAlgebra.single x.toAdd 1)) e).trans ?_
  rw [hj, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
  rfl

theorem pb_mul_aff {Y : Over (Spec ZU.{0})} (g h : Y ⟶ splitTorusAff ZU X) (x : X) :
    pb (A := AddMonoidAlgebra ZU.{0} X) (g * h).left (AddMonoidAlgebra.single x 1) =
      pb (A := AddMonoidAlgebra ZU.{0} X) g.left (AddMonoidAlgebra.single x 1) *
        pb (A := AddMonoidAlgebra ZU.{0} X) h.left (AddMonoidAlgebra.single x 1) := by
  let A := AddMonoidAlgebra ZU.{0} X
  let q : Y.left ⟶ Spec (CommRingCat.of (A ⊗[ZU.{0}] A)) := (lift g h).left ≫ (pullbackSpecIso ZU.{0} A A).hom
  have e0 : (g * h).left = q ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A : A →+* A ⊗[ZU.{0}] A)) := rfl
  have e1 : q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = g.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A)).trans
      (congrArg (·.left) (lift_fst g h)))
  have e2 : q ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) = h.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A)).trans
      (congrArg (·.left) (lift_snd g h)))
  rw [e0, ← e1, ← e2, pb_spec, pb_spec, pb_spec, ← map_mul]
  congr 1
  simp [A, AddMonoidAlgebra.comul_single]

theorem chi_mul {Y : Over S} (g h : Y ⟶ splitTorus S X) (x : Multiplicative X) :
    chi (g * h).left x = chi g.left x * chi h.left x := by
  let g' := ofPull (toZ S) (splitTorusAff ZU X) g
  let h' := ofPull (toZ S) (splitTorusAff ZU X) h
  have e : g * h = toPull (toZ S) (splitTorusAff ZU X) (g' * h') :=
    ((map_mul (toPullHom (toZ S) (splitTorusAff ZU X) Y) g' h').trans
      (congrArg₂ (· * ·) (toPull_ofPull _ _ g) (toPull_ofPull _ _ h))).symm
  have e' : (g * h).left ≫ torFst S X = (g' * h').left := by
    rw [e]
    exact toPull_fst _ _ _
  rw [chi_apply, e']
  exact pb_mul_aff g' h' x.toAdd

theorem chi_one (Y : Over S) (x : Multiplicative X) : chi (1 : Y ⟶ splitTorus S X).left x = 1 := by
  have h := chi_mul (1 : Y ⟶ splitTorus S X) 1 x
  rw [_root_.mul_one] at h
  have hu : IsUnit (chi (1 : Y ⟶ splitTorus S X).left x) := (Group.isUnit x).map _
  exact (hu.mul_eq_left.1 h.symm)

theorem chi_pow {Y : Over S} (g : Y ⟶ splitTorus S X) (x : Multiplicative X) (n : ℕ) :
    chi (g ^ n).left x = chi g.left x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pow_eq_one_iff_chi {Y : Over S} (g : Y ⟶ splitTorus S X) (n : ℕ) :
    g ^ n = 1 ↔ ∀ x, chi g.left x ^ n = 1 := by
  refine ⟨fun h x => by rw [← chi_pow, h, chi_one], fun h => Over.OverMorphism.ext (chi_ext ?_ fun x => ?_)⟩
  · exact (Over.w _).trans (Over.w _).symm
  · rw [chi_pow, h, chi_one]

end PositivityTheory.HtPt.Mh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RedOmHTBc
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem red_omHT_bc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv _ κ' V _ _ _ _
    Ω' _ _ _ _ P ι hred σ σ' d hφ hd hκ hproj
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have := isFractionRing_of_integers hv
  have hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1
      ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)
  obtain ⟨hd', h1, h2, h3, -⟩ := red_proj A K hAK E c hc p R N Ω D C v O hv κ' V Ω'
    (algebraMap A O) P ι hred σ σ' d hσ hφ hd hκ
  have hδ : algebraMap O C (algebraMap A O d) ≠ 0 :=
    (different_generator_dualInt O C E σ' _ hv.hom_inj
      (exists_diff_generator C v O hv E σ').1 hd').1
  obtain ⟨j₀, hj₀, -, hj₀'⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  have hfg : (D.omHT σ).FG := by
    have : IsNoetherian A D.om := isNoetherian_of_fg_of_noetherian _ D.om_lat.fg
    have h := (IsNoetherian.noetherian (D.om'.comap D.om.subtype)).map D.om.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (om'_le_om D)] at h
    exact h.map _
  have : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hfg
  let α : D.omHT σ →ₗ[A] D.om := LinearMap.codRestrict D.om (d • (D.omHT σ).subtype) (by
    rintro ⟨_, x, hx, rfl⟩
    exact h1 x (om'_le_om D hx))
  let β : D.om →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ)
    ((eigProj D.ρΩ σ).restrictScalars A ∘ₗ ((p : A) ^ R • D.om.subtype))
    (fun x => ⟨_, pow_smul_mem_om' D x.2, rfl⟩)
  have hβα : β ∘ₗ α = ((p : A) ^ R * d) • LinearMap.id := by
    ext z
    change eigProj D.ρΩ σ ((p : A) ^ R • d • (z : Ω)) = ((p : A) ^ R * d) • (z : Ω)
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp _ _ D.om' z.2), mul_smul]
  have hne : algebraMap A O ((p : A) ^ R * d) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) hδ h'
  have hα : Function.Injective (α.baseChange O) := by
    have h : Function.Injective ((β.baseChange O) ∘ₗ (α.baseChange O)) := by
      rw [← LinearMap.baseChange_comp, hβα, LinearMap.baseChange_smul, LinearMap.baseChange_id]
      intro x y e
      change ((p : A) ^ R * d) • x = ((p : A) ^ R * d) • y at e
      rw [← algebraMap_smul O, ← algebraMap_smul O ((p : A) ^ R * d) y] at e
      exact smul_right_injective _ hne e
    exact Function.Injective.of_comp h
  obtain ⟨j₁, hj₁, hr₁⟩ := exists_lift (ι.comp α)
  have hj₁' : j₁ = j₀ ∘ₗ α.baseChange O := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul o z =>
      have : o ⊗ₜ[A] z = o • ((1 : O) ⊗ₜ[A] z) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, hj₁, LinearMap.comp_apply j₀, LinearMap.baseChange_tmul, hj₀']
      rfl
  let s : Ω' →ₗ[O] Ω' :=
    ((algebraMap O C (algebraMap A O d))⁻¹ • (LinearMap.id : Ω' →ₗ[C] Ω')).restrictScalars O
  have hs : ∀ w, algebraMap A O d • s w = w := fun w => by
    change algebraMap A O d • (algebraMap O C (algebraMap A O d))⁻¹ • w = w
    rw [← algebraMap_smul C, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinj : Function.Injective (s ∘ₗ j₁) := by
    have hs' : Function.Injective s := fun x y e => by rw [← hs x, e, hs]
    rw [hj₁']
    exact hs'.comp (hj₀.comp hα)
  have hrange : LinearMap.range (s ∘ₗ j₁) = P.omHT σ' := by
    have e : Set.range (ι.comp α) = ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z} := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨α z, ⟨z, z.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
        exact ⟨⟨z, hz⟩, congrArg ι (Subtype.ext e.symm)⟩
    rw [LinearMap.range_comp, hr₁, e, h3, ← Submodule.map_comp]
    have : s ∘ₗ (algebraMap A O d • LinearMap.id) = LinearMap.id := by
      ext w
      change s (algebraMap A O d • w) = w
      rw [map_smul, hs]
    rw [this, Submodule.map_id]
  refine ⟨s ∘ₗ j₁, hinj, hrange, fun z y e => ?_, ?_⟩
  · rw [LinearMap.comp_apply, hs, hj₁]
    exact congrArg ι (Subtype.ext e.symm)
  · have hl := (pt_om_block C v O hv E c hc κ' N V Ω' P σ').2.2.1
    have hfull : (latIn (P.omHT σ') (P.Ωsp σ')).IsFullLattice C := by
      refine { toIsLattice := hl, span_eq_top := ?_ }
      apply eq_top_iff.mpr
      intro x _
      have hx : (x : Ω') ∈ Submodule.span C (P.om : Set Ω') := by
        rw [P.om_lat.span_eq_top]
        trivial
      obtain ⟨a, ha, hay⟩ := exists_smul_mem_of_mem_span_val hv P.om hx
      obtain ⟨z, hz, hze⟩ := P.κ_mem (a • (x : Ω')) hay
      have hm : (algebraMap O C κ' * a) • x ∈ latIn (P.omHT σ') (P.Ωsp σ') := by
        change (algebraMap O C κ' * a) • (x : Ω') ∈ P.omHT σ'
        refine ⟨P.ht z, ⟨z, hz, rfl⟩, ?_⟩
        rw [hze, ← algebraMap_smul C, smul_smul]
        change eigProj P.ρΩ σ' ((algebraMap O C κ' * a) • (x : Ω')) = _
        rw [map_smul, LatBasic.eigProj_of_mem x.2]
      have hm' := Submodule.subset_span hm (R := C)
      have hn : algebraMap O C κ' * a ≠ 0 := mul_ne_zero P.κ_ne ha
      have := (Submodule.span C (latIn (P.omHT σ') (P.Ωsp σ') : Set (P.Ωsp σ'))).smul_mem
        (algebraMap O C κ' * a)⁻¹ hm'
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
      exact this
    rw [← finrank_baseChange_flat (O := O), ← LinearMap.finrank_range_of_inj hinj, hrange,
      ← finrank_lattice _ hfull]
    have e : (latIn (P.omHT σ') (P.Ωsp σ')).map ((P.Ωsp σ').subtype.restrictScalars O) =
        P.omHT σ' := by
      rw [LatBasic.map_latIn]
      exact inf_eq_left.2 (LatBasic.eigQuot_le_eigSp _ _ _)
    conv_lhs => rw [← e]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm

theorem chart_rank : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d d' hp hκ hd hd' hP hP' htest
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero] at h'
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h'
  obtain ⟨𝔮, h𝔮⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {(p : A)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hmem : (p : A) ∈ 𝔮 := h𝔮.1.2 (Ideal.mem_span_singleton_self _)
  have hht : 𝔮.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔮) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    rintro rfl
    exact hp0 hmem
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, -, hred⟩ :=
    htest 𝔮 hprime hht hmem
  let _ : Algebra A O := φ.toAlgebra
  have hg : Function.Injective ((algebraMap O C).comp φ) := hv.hom_inj.comp hφ
  let ψ : K →+* C := IsFractionRing.lift hg
  have hψ : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h]
    exact (IsFractionRing.lift_algebraMap hg a').symm
  have hκ' : φ κ ∣ (p : O) ^ R := by
    have := map_dvd φ hκ
    rwa [map_pow, map_natCast] at this
  obtain ⟨_, -, -, -, e1⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ
    (ψ.comp σ) d (hψ σ) hd hκ' hP
  obtain ⟨_, -, -, -, e2⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) (ψ.comp (σ.comp c.toRingHom)) d' (hψ _) hd' hκ' hP'
  rw [e1, e2]
  exact finrank_Ω_add_Ω P hv hc (ψ.comp σ)

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}

theorem pt_zero (hpt : IsTorsPts G p pt) : pt 0 = 1 := by
  have h := hpt.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul (hpt : IsTorsPts G p pt) (n : ℕ) (x : N) : pt (n • x) = pt x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, pt_zero hpt]
  | succ n ih => rw [succ_nsmul, hpt.add, ih, pow_succ]

theorem exists_pts (T : TorsRep G p) (hpt : IsTorsPts G p pt) :
    ∃ φ : N → (T.A →ₐ[R] R), ∀ x, spMap (φ x) ≫ T.y = pt x := by
  choose φ hφ using fun x => (T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)).exists
  exact ⟨φ, hφ⟩

omit [AddCommGroup N] in
theorem mem_torsFun {C : Type} [Field C] [Algebra R C] (T : TorsRep G p)
    {φ : N → (T.A →ₐ[R] R)} (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (g : N → C) :
    g ∈ torsFun C T pt ↔ ∃ a : T.A, g = fun x => algebraMap R C (φ x a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x _ (hφ x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x ψ h => ?_⟩
    rw [tors_ext T (h.trans (hφ x).symm)]

omit [AddCommGroup N] in
theorem mem_vanIdeal (T : TorsRep G p) {φ : N → (T.A →ₐ[R] R)}
    (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (K : Set N) (a : T.A) :
    a ∈ vanIdeal T pt K ↔ ∀ k ∈ K, φ k a = 0 := by
  constructor
  · exact fun h k hk => h k hk _ (hφ k)
  · intro h k hk ψ e
    rw [tors_ext T (e.trans (hφ k).symm)]
    exact h k hk

end

theorem tors_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt
  obtain ⟨Δ, ε, s, hΔ, -, -, h1, h2, h3, h4, h5⟩ := tors_alg R p G T
  obtain ⟨φ, hφ⟩ := exists_pts T hpt
  have hsurj : ∀ ψ : T.A →ₐ[R] R, ∃ x, spMap ψ ≫ T.y = pt x := fun ψ =>
    ((hpt.range _).1 (tors_pow T ψ)).imp fun _ h => h.symm
  have hbij : Function.Bijective φ :=
    ⟨fun x y h => hpt.inj (by rw [← hφ, ← hφ, h]),
      fun ψ => (hsurj ψ).imp fun x h => tors_ext T ((hφ x).trans h.symm)⟩
  let : Bialgebra R T.A := Bialgebra.ofAlgHom Δ ε h1 h2 h3
  let : HopfAlgebra R T.A := HopfAlgebra.ofAlgHom s h4 (by
    change AlgHom.comp _ Δ = AlgHom.comp _ ε
    rw [← h4]
    conv_lhs => rw [← h5, ← AlgHom.comp_assoc]
    congr 1
    ext <;> simp)
  have : Coalgebra.IsCocomm R T.A := ⟨congr(($h5).toLinearMap)⟩
  have := T.fin
  have := T.free
  obtain ⟨hsep, -, AA, hAA⟩ := hopfalg p C v R hv hp T.A N φ hbij (fun x y a => by
    have : φ (x + y) = (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      apply tors_ext T
      rw [lift_comul T Δ hΔ, Algebra.TensorProduct.lift_comp_includeLeft,
        show (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp
          Algebra.TensorProduct.includeRight = φ y by ext; simp, hφ, hφ, hφ, hpt.add]
    rw [this]
    rfl)
  refine ⟨⟨AA, ?_⟩, fun a ha => hsep a fun x => ha _, fun x => ?_, hsurj, fun x => hpt.inj ?_⟩
  · ext g
    rw [hAA, mem_torsFun T hφ]
  · exact T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  · rw [pt_nsmul hpt, pt_zero hpt]
    exact (hpt.range _).2 ⟨x, rfl⟩

end PositivityTheory.HtPt.Rf
end

