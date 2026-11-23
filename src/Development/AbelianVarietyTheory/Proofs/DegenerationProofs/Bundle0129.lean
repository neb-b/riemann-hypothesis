module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

theorem exists_fibre_pull (laws : Laws) {S S' Z Z' : Scheme.{0}} {j : Z ⟶ S} {j' : Z' ⟶ S'} {f : S' ⟶ S} {ψ : Z' ⟶ Z}
    (sq : ψ ≫ j = j' ≫ f) {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (A : PolAV Z)
    (gen : (Over.pullback j).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom j))) :
    ∃ (A' : PolAV Z') (gen' : (Over.pullback j').obj ((Over.pullback f).obj G) ≅ A'.A),
      IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) ((L.pull (pullback.fst G.hom f)).pull
        (pullback.fst ((Over.pullback f).obj G).hom j')) := by
  obtain ⟨A', g, hg, -, mul, t, ht⟩ := laws.polBaseChange _ _ ψ A
  have pg : IsGrpPullback A'.A A.A ψ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have h₂ := (pg.comp ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G j))).congr
    ((congrArg _ (Category.id_comp _)).trans sq) rfl
  obtain ⟨gen', hgen', e⟩ := grpPullback_iso ((isGrpPullback_pullback _ j').comp
    (isGrpPullback_pullback G f)) h₂
  have hi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, gen.inv_hom_id, Over.id_left]
  refine ⟨A', gen', hgen', LBIso.trans (LB.isLB_pull A'.isLB _) (LB.isLB_pull (LB.isLB_pull A.isLB g) gen'.hom.left)
    (LB.isLB_pull (LB.isLB_pull hL _) _) ?_ ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm ⟨t, ht⟩)
  · refine LBIso.chartPull (h := gen'.hom.left ≫ g ≫ gen.inv.left)
      (chartPullLinComb A.L g _ (fun _ : PUnit => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb L _ _ (fun _ : PUnit => pullback.fst G.hom j) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hi, Category.comp_id]
    · rw [Category.assoc, Category.assoc]
      exact e.symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_generic_square {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (φ : R →+* V) (hφ : Function.Injective φ) :
    ∃ ψ : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of (FractionRing R)),
      ψ ≫ jK R = jK V ≫ spMap φ := by
  have gen : ∀ (K F : Type) [Field K] [Field F] [Algebra R K] [IsFractionRing R K] (g : R →+* F),
      Function.Injective g → ∃ ψ : K →+* F, ψ.comp (algebraMap R K) = g := fun K F _ _ _ _ g hg =>
    ⟨IsFractionRing.lift hg, RingHom.ext fun x => IsFractionRing.lift_algebraMap hg x⟩
  obtain ⟨ψ, hψ⟩ := gen (FractionRing R) (FractionRing V) ((algebraMap V (FractionRing V)).comp φ)
    ((IsFractionRing.injective V (FractionRing V)).comp hφ)
  exact ⟨spMap ψ, (spMap_comp _ ψ).trans ((congrArg spMap hψ).trans (spMap_comp φ _).symm)⟩

theorem exists_desc_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} (pF : IsGrpPullback G' G f F)
    (Q : TQ G X) {P : CP G} (D : Q.Desc P) {P' : CP G'} {hw w} (k : IsCPMap P' P f F hw w) :
    ∃ (Q' : TQ G' X) (D' : Q'.Desc P') (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f β ∧
      LBIso D'.M.L.L (D.M.L.L.pull β) := by
  obtain ⟨Q₀, hQ⟩ := exists_tq_baseChange _ _ _ X _ _ F pF Q
  obtain ⟨β, eβ, pβ⟩ := TQ.exists_isGrpPullback _ _ _ X _ _ F pF Q Q₀ hQ
  obtain ⟨M₀, v, hv⟩ := exists_pull (hw := pβ.1.w) D.M
    (fun Z x y => Over.OverMorphism.ext (pβ.2 Z x y _ _ rfl rfl).symm)
  obtain ⟨w₄, -, k₄⟩ := D.map.exists_comp k (by rw [Category.assoc, Over.w, hw, Category.comp_id])
  obtain ⟨w₅, k₅⟩ := cpMap_congr ((Category.comp_id _).trans (Category.id_comp _).symm) eβ.symm k₄
    (by rw [Category.assoc, pβ.1.w, Over.w_assoc, Category.id_comp])
  have := Q₀.q_hom
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P' _ _ _ Q₀.q.left (by simp) _ hv).2
    (toBase_mul_of_isMonHom Q₀.q _) w₅ k₅
  exact ⟨Q₀, ⟨M₀, w₆, k₆⟩, β, pβ, v, hv.gen⟩

theorem exists_fourth {S S' Z Z' : Scheme.{0}} {t : Z ⟶ S} {t' : Z' ⟶ S'} {f : S' ⟶ S} {b : Z' ⟶ Z}
    (sq : b ≫ t = t' ≫ f) {G : Over S} {G' : Over S'} {H : Over Z} {H' : Over Z'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    {F : G'.left ⟶ G.left} {c : H.left ⟶ G.left} {c' : H'.left ⟶ G'.left} (pF : IsGrpPullback G' G f F)
    (pc : IsGrpPullback H G t c) (pc' : IsGrpPullback H' G' t' c') {P : CP G} {P' : CP G'} {N : CP H} {N' : CP H'}
    {h₁ w₁ h₂ w₂ h₃ w₃} (k₁ : IsCPMap P' P f F h₁ w₁) (k₂ : IsCPMap N P t c h₂ w₂) (k₃ : IsCPMap N' P' t' c' h₃ w₃) :
    ∃ (E : H'.left ⟶ H.left) (pE : IsGrpPullback H' H b E) (w : _), IsCPMap N' N b E pE.1.w w := by
  have p := pc'.comp pF
  have w : (c' ≫ F) ≫ G.hom = (H'.hom ≫ b) ≫ t := p.1.w.trans (by rw [Category.assoc, sq])
  have e₁ := pc.1.lift_fst _ _ w
  have e₂ := pc.1.lift_snd _ _ w
  have p' := p.congr sq.symm e₁.symm
  have pE := pc.cancel p' e₂
  obtain ⟨w₄, -, k₄⟩ := k₁.exists_comp k₃ p.1.w
  obtain ⟨w₅, k₅⟩ := cpMap_congr sq.symm e₁.symm k₄ p'.1.w
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ N' _ _ _ _ e₂ _ k₂).2
    (fun Z x y => Over.OverMorphism.ext (pE.2 Z x y _ _ rfl rfl).symm) w₅ k₅
  exact ⟨_, pE, w₆, k₆⟩

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) {k : Type}
    [Field k] (a : R ⧸ I ^ (0 + 1) →+* k) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V)
      (b : R ⧸ I ^ (0 + 1) →+* V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), CDVR V ∧ Function.Injective φ ∧
      RingHom.ker a = RingHom.ker b ∧ spMap b ≫ thick R I 0 = thick V _ 0 ≫ spMap φ := by
  have := RingHom.ker_isPrime a
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := exists_cdvr R ((RingHom.ker a).comap (Ideal.Quotient.mk _))
  have hm' : (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ = (RingHom.ker a).comap (Ideal.Quotient.mk _) := by
    rw [← hm, zero_add, pow_one]
  have le : I ^ (0 + 1) ≤ (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ := fun r hr => by
    rw [hm', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact zero_mem _
  refine ⟨V, _, ‹_›, ‹_›, φ, Ideal.quotientMap (IsLocalRing.maximalIdeal V ^ (0 + 1)) φ le, hV, hφ,
    Ideal.ext fun y => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.mem_comap, ← hm', RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]


set_option maxHeartbeats 800000 in
theorem main : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  intro laws _ _ hU R _ _ _ I ⟨⟨hN, _⟩, _, hc, _⟩ G _ _ P hG ⟨w, _, hw, _, _, prim, _⟩ A gen hgen hA X _ _ _ T k _ x
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := exists_trait R I a
  obtain ⟨ψ, sq'⟩ := exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  have prim' := prim_pull (spMap φ) prim
  rw [← hP'] at hA' prim'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom (spMap φ)); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ)
      let em := (Functor.mapMonNatIso (Over.pullbackComp q (spMap φ)) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ spMap φ)).obj G ≅ (Over.pullback q).obj ((Over.pullback (spMap φ)).obj G) := (Mon.forget _).mapIso em
      haveI : IsMonHom e.hom := by
        show IsMonHom em.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      exact ⟨{ X := E.X
               addCommGroup := E.addCommGroup
               free := E.free
               finite := E.finite
               B := E.B
               grpB := E.grpB
               isAbelian := E.isAbelian
               q := e.inv ≫ E.q
               q_hom := inferInstance
               q_flat := by rw [Over.comp_left]; have := E.q_flat; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_surjective := by rw [Over.comp_left]; have := E.q_surjective; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               i := E.i ≫ e.hom
               i_hom := inferInstance
               isKernel := by refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have ev := _root_.GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre laws V hV A' _ hG' gen' hgen' P' ((Over.pullback (spMap φ)).map w) inferInstance
    prim' X Q₀ P₀ ⟨w₀, H₀⟩
  obtain ⟨wA, hwA⟩ := hA'
  have pol := pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

end GlobalTheory.ClosedPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesExist
open GlobalTheory.TorusExt GlobalTheory.IndivisibleSection

section Sym
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
  {s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])}

theorem prod_sym {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[A]).left, 𝟙 A.left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp [Hom.inv_def]

theorem val_sym_one (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) : val s (1 : T ⟶ A).left z J = 1 := by
  have := val_corr hJ hr (toUnit T).left
  rw [val_one, val_pull hJ] at this
  exact this

theorem val_sym_mul (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hg : s.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) (x y : T ⟶ A) :
    val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ = val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := by
  have vs : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (r : T ⟶ A ⊗ A) (a : A ⊗ A ⟶ A),
      val (LB.pullGen L.L _ _ s a.left) r.left z J = val s (r ≫ a).left z J := fun hJ r a => val_pull hJ _ _ _
  have v : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (x y : T ⟶ A),
      val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A * snd A A).left)
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (fst A A)⁻¹ (snd A A)⁻¹)).left)) (lift x y).left z J =
        val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ ∧
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A).left)
        (LB.pullGen L.L _ _ s (snd A A).left))
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (snd A A) (lift (snd A A)⁻¹ (fst A A))).left)) (lift x y).left z J =
        val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := fun hJ x y => by
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (val_cub c _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs hJ _ _) (vs hJ _ _))) (val_cub c _ hJ _ _ _))).trans ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  rw [← (v hJ x y).1, ← (v hJ x y).2]
  refine gen_unique' L.isLB (fun U _ h => ?_) (A ⊗ A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left
    (Over.w _) hs
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _)
      (DVR.pullGen_isGen _ _ _ _ hg _)) (DVR.pullGen_isGen _ _ _ _ c.isGen _)) (fun w I hI => ?_) _ _ z J hJ
  · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_sym _ h) (prod_sym _ h))) (prod_cub _ _ _ h))).trans
      (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_cub _ _ _ h))).symm)
    simp only [mul_inv_cancel, _root_.one_mul, mul_inv, mul_comm (snd A A) (fst A A), mul_comm (snd A A)⁻¹ (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (v (T := 𝟙_ (Over S)) hI 1 1).1.trans (Eq.trans ?_ (v (T := 𝟙_ (Over S)) hI 1 1).2.symm)
    simp only [_root_.mul_one, inv_one, val_sym_one (T := 𝟙_ (Over S)) hr hI]
end Sym

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem coe_val (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    ((stalkUnits z).symm (val t r z J) : F) = vF t r J := by
  refine (stalkConst z).injective ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)
end Val

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_th (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ th : H0 D.P.L 1, ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j := by
  have hL := D.P.isLB
  obtain ⟨b, hb⟩ := exists_generator D hS
  obtain ⟨th, hth⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by rw [prod_fam_zero]; simp) b
  refine ⟨th, fun s => ?_⟩
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := D.famφB 0) (ε' := DegPre.famε 1)
    (fun U _ h => by rw [prod_fam_zero]; simp) s
  obtain ⟨a, ha, -⟩ := hb s'
  refine ⟨a, secIsMul_of_sval hL fun y J hJ => ?_⟩
  rw [← hs' _ _ y J hJ, sval_of_secIsMul ha _ y hJ, hth _ _ y J hJ, Category.id_comp]

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_ext (S : ValuationSubring F) (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

theorem exists_gauge (S : ValuationSubring F) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ ψ, (∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U (J ψ) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ((∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart hL (x₀ (IsLocalRing.closedPoint S))
      have e : x₀ ⁻¹ᵁ L.U j = ⊤ := DVR.eq_top_of_closedPoint_mem _ hj
      exact ⟨j, fun w _ => e.ge (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, e.ge⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ (IsLocalRing.closedPoint F))
      exact ⟨j, (DVR.eq_top_of_closedPoint_mem (ψ ⁻¹ᵁ L.U j) hj).ge, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, h₂⟩

theorem exists_numOf (hG : GlobalFnsSt) (he : D.PsiEven) (hb : D.TauBimult) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ : Good D.P.L z J := fun ψ => good ψ trivial
  let e := (stalkUnits z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _)))
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))
  have hx : ∀ χ, jFK (R := R) F ≫ D.xK χ = (DegPre.cF D F χ).left := fun χ => (Category.assoc _ _ _).symm
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y u => e (cubV D.cub (T := TF (R := R) F) z J x y u)
      cub := ⟨fun x y => by rw [C.face, map_one], fun x y u => by rw [C.s01], fun x y u => by rw [C.s12],
        fun x x' x'' y => by rw [← map_mul, ← map_mul, C.coc]⟩
      σ := fun x => e (val D.sym x.left z J)
      σ_one := (congrArg e (val_sym_one (L := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩) D.sym_rig
        (T := TF (R := R) F) hJ)).trans (map_one e)
      σ_mul := fun x y => by
        rw [← map_mul, ← map_mul, ← map_mul]
        exact congrArg e (val_sym_mul D.cub sj D.sym_gen D.sym_rig (T := TF (R := R) F) hJ x y)
      th := fun x => sF th x.left J * ((e ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a b => by
        rw [DegPre.cF, D.c_add]
        exact MonObj.comp_mul _ _ _
      ψ := fun χ => e (p χ * ρ)
      even := fun χ => by
        have h := val_corr hJ (he χ) (jFK (R := R) F)
        rw [val_mul hJ, val_pull hJ, hx] at h
        rw [← map_mul, mul_right_comm]
        exact congrArg (fun q => e (q * ρ)) h
      bimult := fun a a' b => by
        have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (val_pull hJ _ _ _))).symm.trans
          ((val_corr hJ (hb a a' b) (jFK (R := R) F)).trans
            ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (hτ _ _))))
        have h3 : jFK (R := R) F ≫ D.pt3 a a' b =
            (lift (DegPre.cF D F a) (lift (DegPre.cF D F a') (DegPre.cF D F b))).left := by
          let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
          refine congrArg CommaMorphism.left (show κ ≫ lift _ (lift _ _) = _ from ?_)
          simp only [comp_lift, comp_toUnit_assoc]
        rw [h3] at h
        simp only [← map_div, ← map_mul]
        refine congrArg e ?_
        have k : ∀ u v w, (u * ρ) / (v * ρ) / (w * ρ) = u * v⁻¹ * w⁻¹ * ρ⁻¹ := fun u v w => by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_div]
          abel
        rw [k, k, k]
        exact h }
  have hρ : (e ρ : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom J := coe_val _ _ hJ
  exact ⟨N,
    { J := J, good := good, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun x y u => coe_val _ _ hJ
      σ_eq := fun x => coe_val _ _ hJ
      th_eq := fun x => by
        rw [← hρ]
        exact Units.inv_mul_cancel_right _ _
      ψ_eq := fun χ => by
        rw [← hρ, ← coe_val _ _ hJ]
        exact (congrArg Units.val (map_mul e _ _)).trans (Units.val_mul _ _) }, rfl⟩

theorem exists_integral_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  intro hL R _ _ _ _ D he hb F _ _ S hS
  obtain ⟨th, hth⟩ := exists_th D hL.secBaseChange
  obtain ⟨J, good, hJ⟩ := exists_gauge F S D.P.isLB
  obtain ⟨N, ν, rfl⟩ := exists_numOf D F hL.globalFns he hb th hth J good
  exact ⟨N, ν, fun x => hJ _ (exists_ext D F S hS x)⟩

end GlobalTheory.ValuesExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomComplexOfCountableOfRelations
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
end

