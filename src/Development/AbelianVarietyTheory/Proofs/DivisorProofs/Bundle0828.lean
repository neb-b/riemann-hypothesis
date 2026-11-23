module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem push_comp (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A} (hab : α.left ≫ φ = φ ≫ β.left)
    (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem isTanScal_iff (h : IsGrpPullback A' A f φ) {O : Type} [Ring O] (a : OActN O A) (a' : OActN O A')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ A') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A'), u.left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ w.left ↔
      (e u).left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ (e w).left := fun u w => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    have H := hR (v ≫ a'.act b) v
    rw [E] at H
    exact H

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem kernel_pullback (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (e : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ e = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine GlobalTheory.SiegelPull.push_injective h T ((map_pow _ _ _).trans ((hn _ (pushHom h T x) ?_).trans (map_one _).symm))
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_objMap_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb D.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  obtain ⟨eK, heK, hK⟩ := o.kerP
  let o' : Obj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      kerP := ⟨eK, heK, fun T x hx => kernel_pullback pb sq o.isLB hP' iso eK hK T x hx⟩
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A A' f φ (o.act.toF D) (actN.toF D) pb
        (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end GlobalTheory.HTPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open Filter Topology Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeTensorRead

theorem continuous_of_map_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    (g : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hg : ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ v, g a v ∈ v.adicCompletionIntegers E) :
    Continuous g := by
  refine continuous_of_continuousAt_zero g.toAddMonoidHom ?_
  intro U hU
  have hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 E) E) := by simpa using hU
  have hC := GlobalTheory.AdeleCocompact.isCompact_integral E
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (0 : FiniteAdeleRing (𝓞 E) E)) (P := fun x y => x * y ∈ U)
    (fun y _ => (continuous_mul.tendsto' ((0 : FiniteAdeleRing (𝓞 E) E), y) 0 (zero_mul y)) hU0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually h1).exists
  have hn0 : ((n.factorial : ℕ) : F) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  let m : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((n.factorial : ℕ) : F)⁻¹
  have hm : ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * m = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have h2 : (fun a => m * a) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∈ 𝓝 0 :=
    (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by
      intro v
      change (m * 0) v ∈ _
      rw [mul_zero]
      exact zero_mem _)
  refine Filter.mem_map.2 (mem_of_superset h2 fun a ha => ?_)
  have h3 := hn _ (hg _ ha)
  rw [← map_natCast g, ← map_mul, ← mul_assoc, hm, one_mul] at h3
  exact h3

theorem continuous_finite_equiv (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    Continuous ι ∧ Continuous ι.symm := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (Af D.host.F ⊗[D.host.F] D.host.E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Af D.host.F ⊗[D.host.F] D.host.E) := e0.secondCountableTopology
  have hc : Continuous ι := by
    refine IsModuleTopology.continuous_of_ringHom (R := Af D.host.F) ι.toRingHom ?_
    refine continuous_of_map_integral _ fun a ha P => ?_
    exact (hint (a ⊗ₜ[D.host.F] (1 : D.host.E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P
  have ho : IsOpenMap ι :=
    AddMonoidHom.isOpenMap_of_sigmaCompact ι.toAddEquiv.toAddMonoidHom ι.surjective hc
  exact ⟨hc, (ι.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous⟩

theorem exists_infinite_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  haveI := h.1
  haveI := h.2.1
  choose θ h1 h2 using fun w : InfinitePlace E => GlobalTheory.InfAdeleCM.exists_hom (F := F) w.embedding
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ (InfinitePlace E) (fun w => w.embedding) θ h
    (by
      unfold GlobalTheory.Mem.Vol.IsCMFam
      simp only [InfinitePlace.mk_embedding]
      exact Function.bijective_id) (fun w => ⟨h1 w, h2 w⟩)
  let p : InfiniteAdeleRing E ≃+* (InfinitePlace E → ℂ) :=
    RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  have hp : Continuous p := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have hp' : Continuous p.symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)
  refine ⟨e.trans p.symm, hp'.comp hc, hc'.comp hp, fun x => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  funext w
  rw [he, h1]
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  simpa using (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)).symm

theorem isPlIdem_parts (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) :
    infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ Q, Q ≠ P → ι (finPart D e) Q = 0 := by
  obtain ⟨hee, ⟨v, ε, ⟨α, rfl, -, -⟩, hor⟩, hx⟩ := he
  have hε1 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  have hinf : infPart D e = 0 := by
    rcases hor with ⟨h1, h2⟩ | h
    · have : e = e * (e + cA D e) := by rw [mul_add, hee, h1, add_zero]
      rw [this, h2, RingHom.map_mul, hε1, mul_zero]
    · rw [h, hε1]
  obtain ⟨f, hf⟩ : ∃ f, f = ι (finPart D e) := ⟨_, rfl⟩
  have hff : f * f = f := by rw [hf, ← map_mul, ← RingHom.map_mul, hee]
  have hf01 : ∀ R, f R ≠ 0 → f R = 1 := by
    intro R hR
    have : f R * f R = f R * 1 := by rw [← GlobalTheory.PlaceIdem.mul_ap, hff, mul_one]
    exact mul_left_cancel₀ hR this
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, f R ≠ 0 ∧ x ∈ R.asIdeal) := by
    intro x hx0
    have h1 : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
    rw [hx x hx0, hint, RingHom.map_mul, map_mul, ← hf, h1, hι, not_forall]
    refine exists_congr fun R => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap]
    by_cases hR : f R = 0
    · simp [hR]
    · rw [hf01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]
      simp
  have h0 : ∀ Q, Q ≠ P → f Q = 0 := by
    intro Q hQ
    by_contra hne
    refine hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (key x hx0).2 ⟨Q, hne, hxQ⟩
  rw [← hf]
  refine ⟨hinf, ?_, h0⟩
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  obtain ⟨R, hR, -⟩ := (key x hx0).1 hxP
  by_cases hRP : R = P
  · subst hRP
    exact hf01 _ hR
  · exact absurd (h0 R hRP) hR

theorem map_loc {R S : Type} [CommRing R] [CommRing S] (q : R →+* S) (e a : R) :
    q (1 + e * (a - 1)) = 1 + q e * (q a - 1) := by
  simp

theorem loc_eq_finSingle {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f a : FiniteAdeleRing (𝓞 E) E) (k : E) (ha : a = algebraMap E _ k) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    1 + f * (a - 1) = Neutral.B1.finiteSingle E P (algebraMap E _ k) := by
  subst ha
  refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
  classical
  change 1 + f Q * (algebraMap E (Q.adicCompletion E) k - 1) =
    Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) P (algebraMap E _ k) Q
  by_cases hQ : Q = P
  · subst hQ
    rw [h1, Function.update_self]
    ring
  · rw [h0 Q hQ, Function.update_of_ne hQ]
    ring

theorem exists_adele_tensor_equiv (D : D7) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) = ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨hιc, hιc'⟩ := continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact loc_eq_finSingle P _ _ _ h4 h2 h3

theorem exists_hchar_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c →
    ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  intro D c hc
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  refine ⟨⟨Circle.toUnits.comp (c.comp u), ht.comp (hc.1.comp hu), fun k => ?_⟩, hc, fun P e he k x hx => ?_⟩
  · have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]
  · have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl

end GlobalTheory.HeckeTensorRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralResidueSystemFiniteAdelesMod
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt.Res

open GlobalTheory.CMVal.PicFin

theorem mk_eq_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) (z a : intR E) :
    Ideal.Quotient.mk (Ideal.span {(N : intR E)}) z = Ideal.Quotient.mk _ a ↔
      ∀ w, Valued.v (z.1 w - a.1 w) ≤ radN E N w := by
  have hn0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨β, hβ⟩ w
    have h3 : z.1 - a.1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : z.1 w - a.1 w = algebraMap E (w.adicCompletion E) (N : E) * β.1 w := congrArg (fun y : Af E => y w) h3
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  · intro hz
    refine ⟨⟨algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1), fun P => ?_⟩, Subtype.ext ?_⟩
    · have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hN
      show Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹ * (z.1 P - a.1 P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
    · show z.1 - a.1 = (N : Af E) * (algebraMap E (Af E) (N : E)⁻¹ * (z.1 - a.1))
      rw [← map_natCast (algebraMap E (Af E)), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul]

theorem exists_residues : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E),
    (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) →
      ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  classical
  intro E _ _ N hN
  haveI := finite_quot (E := E) hN.ne'
  haveI := Fintype.ofFinite (intR E ⧸ Ideal.span {(N : intR E)})
  choose s hs using Ideal.Quotient.mk_surjective (I := Ideal.span {(N : intR E)})
  refine ⟨Finset.univ.image fun q => (s q).1, fun a ha w => ?_, fun z hz => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((s q).2 w)
  · let z' : intR E := ⟨z, fun w => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz w)⟩
    refine ⟨(s (Ideal.Quotient.mk _ z')).1, ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (mk_eq_iff hN z' _).1 (hs _).symm⟩, ?_⟩
    rintro a ⟨ha, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    rw [(mk_eq_iff hN z' (s q)).2 h, hs]

end GlobalTheory.CMVal.LatEnt.Res
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  first | (exact @GlobalTheory.LieCoordR.exists_coords_baseChange) | (exact GlobalTheory.LieCoordR.exists_coords_baseChange) | (intros; apply GlobalTheory.LieCoordR.exists_coords_baseChange  <;> assumption)
end

