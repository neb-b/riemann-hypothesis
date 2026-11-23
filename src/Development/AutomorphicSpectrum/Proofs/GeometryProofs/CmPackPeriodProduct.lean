module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMap_comp_alg (f : R →+* R') :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (f : R →+* R') (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (epsMul c) = (epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]

theorem fst_comp_dualMap (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_dualMap (f : R →+* R') (g : R' →+* R'') :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem epsMul_zero_eq : epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

def bar (f : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap f ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap R' (DualNumber R')) ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem exists_bc {G : Over S} (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    (u : epsAt x ⟶ G) : ∃ u' : epsAt x' ⟶ G, u'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ u.left := by
  subst hx
  exact ⟨bar f x ≫ u, rfl⟩

theorem isComb_bc {G : Over S} [GrpObj G] (f : R →+* R') (x : Sp R ⟶ S) {x' : Sp R' ⟶ S} (hx : x' = spMap f ≫ x)
    {n : ℕ} (c : Fin n → R)
    (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G))
    (w' : epsAt x' ⟶ G) (hv : ∀ i, (v' i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (v i).left)
    (hw : w'.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w.left) (h : Fl.IsComb c v w) :
    Fl.IsComb (fun i => f (c i)) v' w' := by
  subst hx
  obtain ⟨u, hu, rfl⟩ := h
  let φ : (epsAt x ⟶ G) →* (epsAt (spMap f ≫ x) ⟶ G) :=
    { toFun := fun y => bar f x ≫ y
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]
  · have e : w' = φ (List.ofFn u).prod := Over.OverMorphism.ext hw
    rw [e, map_list_prod, List.map_ofFn]
    rfl

theorem one_left {G : Over S} [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) : (1 : Over.mk x ⟶ G).left = x ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem isComb_pad {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Sp R ⟶ S} {m M : ℕ} {c : Fin m → R}
    {v : Fin m → (epsAt x ⟶ G)} {w : epsAt x ⟶ G} (C : Fin M → R) (V : Fin M → (epsAt x ⟶ G)) (jj : Fin m → Fin M)
    (hj : Function.Injective jj) (hc : ∀ j, C (jj j) = c j) (hv : ∀ j, V (jj j) = v j)
    (h0 : ∀ q, q ∉ Set.range jj → C q = 0) (ht : ∀ q, IsTanAt G x (V q)) (h : Fl.IsComb c v w) :
    Fl.IsComb C V w := by
  classical
  obtain ⟨u, hu, rfl⟩ := h
  let U : Fin M → (epsAt x ⟶ G) := fun q => if hq : ∃ j, jj j = q then u hq.choose else 1
  have hU : ∀ j, U (jj j) = u j := fun j => by
    have hq : ∃ j', jj j' = jj j := ⟨j, rfl⟩
    simp only [U, dif_pos hq]
    rw [hj hq.choose_spec]
  have hU1 : ∀ q, q ∉ Set.range jj → U q = 1 := fun q hq => by
    simp only [U]
    exact dif_neg hq
  refine ⟨U, fun q => ?_, ?_⟩
  · by_cases hq : q ∈ Set.range jj
    · obtain ⟨j, rfl⟩ := hq
      rw [hU, hu, hc, hv]
    · rw [hU1 q hq, h0 q hq, epsMul_zero_eq, ← spMap_comp_spMap, Category.assoc]
      have := ht q
      unfold IsTanAt at this
      erw [this]
      rw [one_left, one_left]
      rfl
  · rw [List.prod_ofFn, List.prod_ofFn]
    exact Fintype.prod_of_injective jj hj _ _ (fun q hq => hU1 q hq) (fun j => (hU j).symm)

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

variable {S : Scheme.{0}} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem tan_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) (v : epsAt x ⟶ t.G)
    (h : v.left = v'.left ≫ m.φ) : IsTanAt t'.G x' v' ↔ IsTanAt t.G x v := by
  subst hx
  have he : eSec t'.G ≫ m.φ = f ≫ eSec t.G := PolBaseChange.eSec_comm m.cart
  unfold IsTanAt
  rw [one_left, one_left, h]
  constructor
  · intro e
    rw [← Category.assoc, e, Category.assoc, he, Category.assoc]
  · intro e
    refine m.cart.1.hom_ext ?_ ?_
    · have he' : eSec t'.G ≫ m.cm.F = f ≫ eSec t.G := he
      rw [Category.assoc, e, Category.assoc, Category.assoc, he']
    · have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
      have h2 : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, Category.assoc, h1, h2]
      refine Eq.trans ?_ (Category.comp_id x').symm
      erw [← Category.assoc, spMap_comp_spMap]
      have : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
        refine RingHom.ext fun a => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      show Spec.map (𝟙 _) ≫ x' = x'
      rw [Spec.map_id, Category.id_comp]

theorem exists_vec {G : Over (Sp R)} [GrpObj G] (σ : R →+* R') (w : epsR R ⟶ G) :
    ∃ U : epsAt (spMap σ) ⟶ G, U.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left ∧ (IsTangent w → IsTanAt G (spMap σ) U) := by
  have h1 : w.left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := Over.w w
  refine ⟨Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left) (by
    show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ
    rw [Category.assoc, h1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), rfl, fun ht => ?_⟩
  unfold IsTanAt
  rw [one_left]
  unfold IsTangent at ht
  show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ w.left = _
  rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, ht]
  rfl

theorem mono_alg (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {c : Coeff l} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

abbrev sg (X : CMPack Z c FU i hP) (s : X.K →+* ℂ) : 𝓞 X.K →+* ℂ := s.comp (algebraMap (𝓞 X.K) X.K)

theorem exists_lift (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b))
    (u : epsAt (under X.y) ⟶ Xo.univ.t.G) (hu : X.IsImage b a u) (s : X.K →+* ℂ)
    (Ux : epsAt (spMap (sg X s)) ⟶ X.B.t.G)
    (hUx : Ux.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (sg X s)) ≫ (X.C b).v.left ≫ (X.ψ b a).left) :
    ∃ U' : epsAt (spMap s) ⟶ X.t.G, U'.left ≫ X.m.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ u.left ∧ U'.left ≫ X.m'.φ = Ux.left := by
  obtain ⟨ρ, h1, h2⟩ := hu
  have hm := mono_alg X.K
  have hw : ρ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    rw [← cancel_mono (spMap (algebraMap (𝓞 X.K) X.K)), Category.assoc, ← X.m'.cart.1.w, ← Category.assoc, h2,
      Category.assoc, Category.assoc, Over.w (X.ψ b a)]
    have e1 : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
    rw [e1, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]
  refine ⟨Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) (by
    show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap s
    rw [Category.assoc, hw, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg]), ?_, ?_⟩
  · show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.m.φ = _
    rw [Category.assoc, h1]
  · show (spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ ρ) ≫ X.m'.φ = _
    rw [Category.assoc, h2, hUx, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMap]

theorem one_tangent (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)) :
    IsTangent ((X.C b).v ≫ X.ψ b a) := by
  have h1 : IsTangent (X.C b).v := (X.C b).basis.1 0
  have h2 : IsMonHom (X.ψ b a) := ((X.fam b).1 a).isMonHom
  unfold IsTangent at h1 ⊢
  rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, IsMonHom.one_hom]

theorem w_eq (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ) :
    s (X.β (tauE c τ (H.w0 : E))) = sg X s (X.ω b) := by
  show s _ = s _
  congr 1
  refine Subtype.ext ?_
  have e1 := (X.map b).1
  have e2 := (Z b).hω
  have e3 : 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := by
    have h0 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at this
      exact this
    have := congrArg τ h0
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have e4 : (((X.ω b : 𝓞 X.K) : X.K) : ℂ) = (((Z b).ω : (Z b).M) : ℂ) := by rw [← e1]; rfl
  have e5 : ((X.β (tauE c τ (H.w0 : E)) : X.K) : ℂ) = τ (H.w0 : E) := rfl
  rw [e4, e5]
  rw [hτ, ← e2] at e3
  linear_combination (1/2 : ℂ) * e3

def kap (X : CMPack Z c FU i hP) (τ : E →+* ℂ) (s : X.K →+* ℂ) : OK H →+* ℂ :=
  (s.comp (X.β.comp (tauE c τ))).comp ((algebraMap (𝓞 E) E).comp (OK H).val.toRingHom)

theorem gram_family (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = sgnRt H b) (s : X.K →+* ℂ)
    (r : ℝ) (hr : IsLieNormSq (Z b).C.P (Z b).C.v
      ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r)
    {M : ℕ} (aq : Fin M → PureType.lat hP (sgnRt H b)) (Wq : Fin M → (epsAt (under X.y) ⟶ Xo.univ.t.G))
    (hW : ∀ q, X.IsImage b (aq q) (Wq q)) (V : Fin M → (epsAt (under (spMap s ≫ X.y)) ⟶ Xo.univ.t.G))
    (hV : ∀ q, (V q).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ (Wq q).left) :
    (∀ q, IsTanAt Xo.univ.t.G (under (spMap s ≫ X.y)) (V q)) ∧
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ X.y)) V
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
  have hU := fun q => exists_vec (sg X s) ((X.C b).v ≫ X.ψ b (aq q))
  choose U hUl hUt using hU
  have hU' := fun q => exists_lift X b (aq q) (Wq q) (hW q) s (U q) (hUl q)
  choose U' h1 h2 using hU'
  have hnorm : IsLieNormSq (X.C b).P (X.C b).v (sg X s) r :=
    (_root_.GlobalTheory.CompanionTheory.Ar.Fl.lieNormSq_baseChange E H _ _ _ _ (Z b).C (X.C b) _ (X.φ b) (sg X s) r (X.map b)).1 hr
  have hk : kap X τ s (wK H) = sg X s (X.ω b) := w_eq X b τ hτ s
  have g0 : IsHodgeGram X.B.t.G X.B.t.PP.L (spMap (sg X s)) U
      (Matrix.of fun q q' => r * kap X τ s (X.h b (aq q) (aq q'))) := by
    let C := X.C b
    let T := X.B
    let ψ := X.ψ b
    let σ := sg X s
    let κ := kap X τ s
    let h := X.h b
    let L := PureType.lat hP (sgnRt H b)
    let ω := X.ω b
    have hu (k : Fin M) : (U k).left =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap σ) ≫ C.v.left ≫ (ψ (aq k)).left := by
      rw [← Over.comp_left]
      exact hUl k
    obtain ⟨hlin, -, -, hlam⟩ := X.fam b
    obtain ⟨P', φ, v', uC, Hm, χ, w, ⟨hg', hpb, hLB⟩, hvo, hAH, hdw, hrr⟩ := hnorm
    have laws := abelianSchemeLaws_all.1
    obtain ⟨Q, ψQ, hQg, hQpb, hQLB⟩ := exists_isPolFibre laws.polBaseChange σ T.pol
    obtain ⟨rig0, hrig0⟩ := P'.rigid
    obtain ⟨u0, Hm0, χ0, -, hAH0, -, -, d20, hend0, -⟩ := thetaUnifAV_all P' rig0 hrig0
    obtain ⟨rigT, hrigT⟩ := Q.rigid
    obtain ⟨uT, HmT, χT, -, hAHT, -, -, d2T, -, -⟩ := thetaUnifAV_all Q rigT hrigT
    have := T.t.comm
    have := C.P.isAb.comm
    have hψm : ∀ b, IsMonHom (ψ b) := fun b => (hlin b).isMonHom
    choose f hfm hfc using fun a : L =>
      @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hQpb (ψ a) (hψm a)
    choose e hem hec using fun c : OK H =>
      @PairingFibre.exists_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hpb hpb (C.act.act c) (C.act.hom c)
    choose F hFl using fun a : L =>
      @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ uT u0 (f a) (hfm a)
    choose G hGl using fun c : OK H => hend0 (e c) (hem c)
    obtain ⟨K, hK⟩ := @HodgeUnique.exists_linear_compare _ _ _ _ _ _ _ _ u0 uC (𝟙 P'.A) inferInstance
    have hv'T : IsTangent v' := IsVecOver.isTangent hpb hvo (C.basis.1 0)
    have hd0 : u0.IsDiff (K w) v' := by
      simpa using HodgeUniq.isDiff_comp u0 uC d20 (𝟙 P'.A) K hK hv'T hdw
    have hKH : ∀ z z', hermForm Hm0 (K z) (K z') = hermForm Hm z z' :=
      (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq thetaUnifAV_all laws P' P' P' P' uC uC u0 uC Hm0 Hm χ0 χ hAH0 hAH (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
        K K LinearMap.id LinearMap.id hK hK (fun z => by simp) (fun z => by simp)).1 (fun _ _ _ _ _ _ _ => Iff.rfl)
    have hkey : ∀ b b' : L, ∀ z z',
        hermForm HmT (F b z) (F b' z') = hermForm Hm0 (G (h b b') z) z' := by
      intro b b' z z'
      have W0 := (PairingFibre.lamEq_weilEq_over_ring laws (𝓞 X.K) C.P C.P T.pol C.P (ψ b) (ψ b') (C.act.act (h b b'))
        (𝟙 _) (hψm b) (hψm b') (C.act.hom _) inferInstance ℂ σ).1 (hlam b b')
      have hId : (𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ =
          φ ≫ (𝟙 C.P.A : C.P.A ⟶ C.P.A).left := by
        exact (Category.id_comp φ).trans (Category.comp_id φ).symm
      have W1 := (PairingFibre.weilEq_iff hpb hpb hQpb hpb T.t.PP.isLB C.P.isLB Q.isLB P'.isLB
        (LBIso.symm hQLB) (LBIso.symm hLB) (hfc b) (hfc b') (hec (h b b')) hId (𝟙 (Sp ℂ))).2
        (by rw [Category.id_comp]; exact W0)
      have := (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq thetaUnifAV_all laws P' P' Q P' u0 u0 uT u0 HmT Hm0 χT χ0 hAHT hAH0 (f b) (f b')
        (e (h b b')) (𝟙 _) (F b) (F b') (G (h b b')) LinearMap.id (hFl b) (hFl b') (hGl _) (fun z => by simp)).1 W1 z z'
      simpa using this
    have hg1 : P'.g = 1 := hg'.trans C.dim
    choose c hc using fun x : OK H => CurveAdjoint.exists_scalar hg1 (G x)
    have pa : ∀ (b : OK H) (p : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A),
        Geo.Tor.pushHom hpb _ (p ≫ e b) = Geo.Tor.pushHom hpb _ p ≫ C.act.act b := fun b p =>
      Over.OverMorphism.ext (by
        show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
        rw [Category.assoc, hec, Category.assoc])
    have inj : ∀ p q : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A, Geo.Tor.pushHom hpb _ p = Geo.Tor.pushHom hpb _ q → p = q :=
      fun p q e' => SymBaseChange.pushPt_injective hpb e'
    have sc : ∀ (b : OK H) (s : ℂ) (Gs : (Fin P'.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z, Gs z = s • z) →
        (∀ z, u0.ex (G b z) = u0.ex (Gs z)) → c b = s := fun b s Gs hG hh => by
      have e' := congrFun ((hc b 1).symm.trans ((LinearMap.congr_fun (CurveAdjoint.linear_eq_of_ex u0 _ _ hh) 1).trans
        (hG 1))) ⟨0, by omega⟩
      simpa using e'
    let j : OK H →+* ℂ := RingHom.mk'
      { toFun := c
        map_one' := sc 1 1 LinearMap.id (fun z => by simp) fun z => inj _ _ (by
          rw [hGl, pa, C.act.one, Category.comp_id, LinearMap.id_apply])
        map_mul' := fun b b' => sc _ _ (G b' ∘ₗ G b) (fun z => by
          rw [LinearMap.comp_apply, hc, hc, smul_smul, mul_comm]) fun z => inj _ _ (by
            rw [LinearMap.comp_apply, hGl, hGl, hGl, pa, pa, pa, C.act.mul, Category.assoc]) }
      fun b b' => sc _ _ (G b + G b') (fun z => by
        rw [LinearMap.add_apply, hc, hc, ← add_smul]; rfl) fun z => inj _ _ (by
          rw [LinearMap.add_apply, u0.ex_add, map_mul, hGl, hGl, hGl, pa, pa, pa, C.act.add, Hom.mul_def, Hom.mul_def,
            ← Category.assoc, comp_lift])
    have heig : C.v ≫ C.act.act (wK H) = CMCurveTest.scaleVec ω C.v := by
      obtain ⟨u_, hu_, hprod⟩ := C.eig
      rw [hprod]
      apply Over.OverMorphism.ext
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
      exact hu_ 0
    have hover : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (v' ≫ e (wK H)) := by
      show (v' ≫ e _).left ≫ φ = _
      rw [Over.comp_left, Category.assoc, hec, ← Category.assoc, hvo, Over.comp_left, Category.assoc]
    have hsc : IsVecOver σ φ (C.v ≫ C.act.act (wK H)) (CMCurveTest.scaleVec (σ ω) v') := by
      rw [heig]
      exact CMCurveTest.isVecOver_scaleVec hvo ω
    have hvv : v' ≫ e (wK H) = CMCurveTest.scaleVec (σ ω) v' :=
      (existsUnique_isVecOver hpb.1 (C.v ≫ C.act.act (wK H))).unique hover hsc
    have hGw : G (wK H) (K w) = σ ω • K w := by
      have := hem (wK H)
      have h1 := HodgeUniq.isDiff_comp u0 u0 d20 (e (wK H)) (G (wK H)) (hGl _) hv'T hd0
      have h2 := CMCurveTest.isDiff_scaleVec u0 hd0 (σ ω)
      rw [← hvv] at h2
      exact HodgeUnique.eq_of_isDiff u0 (Fl.lie_norm_square_of_family.isTangent_comp hv'T (e (wK H))) h1 h2
    have hjk : K w ≠ 0 → ∀ x, c x = κ x := by
      intro hne x
      have hw : c (wK H) = σ ω := by
        have e' : (c (wK H) - σ ω) • K w = 0 := by rw [sub_smul, ← hc, hGw, sub_self]
        exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right hne)
      obtain ⟨⟨m, k⟩, hx, -⟩ := existsUnique_coord H x
      have hw' : j (wK H) = κ (wK H) := hw.trans hk.symm
      change j x = κ x
      rw [hx, j.map_add, κ.map_add, j.map_mul, κ.map_mul, map_intCast j m, map_intCast j k,
        map_intCast κ m, map_intCast κ k, hw']
    refine ⟨Q, ψQ, fun k => v' ≫ f (aq k), uT, HmT, χT, fun k => F (aq k) (K w), hQpb, hQLB, hAHT,
      fun k => ⟨?_, ?_⟩, fun k k' => ?_⟩
    · rw [Over.comp_left, Category.assoc, hfc, ← Category.assoc, hvo, hu k, Category.assoc]
      rfl
    · have := hfm (aq k)
      exact HodgeUniq.isDiff_comp uT u0 d2T (f (aq k)) (F (aq k)) (hFl _) hv'T hd0
    · simp only [Matrix.of_apply]
      rw [hkey, hc, Fl.lie_norm_square_of_family.hermForm_smul_left, hKH]
      obtain ⟨t, ht⟩ : ∃ t : ℝ, hermForm Hm w w = t := ⟨_, Fl.lie_norm_square_of_family.hermForm_self_eq_re hAH.1 w⟩
      rw [ht] at hrr ⊢
      simp only [Complex.ofReal_re] at hrr
      by_cases hne : K w = 0
      · have h0 : (t : ℂ) = 0 := by rw [← ht, ← hKH, hne]; simp [hermForm]
        have h0' : t = 0 := by exact_mod_cast h0
        rw [hrr, h0']
        simp
      · rw [hjk hne, hrr]
        push_cast
        ring
  have hx1 : spMap (sg X s) = spMap s ≫ spMap (algebraMap (𝓞 X.K) X.K) := (spMap_comp_spMap _ _).symm
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  have hV2 : ∀ q, (V q).left = (U' q).left ≫ X.m.φ := fun q => (hV q).trans (h1 q).symm
  have hU2 : ∀ q, (U q).left = (U' q).left ≫ X.m'.φ := fun q => (h2 q).symm
  have g1 := (_root_.PositivityTheory.Xgf.hodge_gram_invariant_pullback E H _ _ X.B.t X.t _ X.m' (spMap s) (spMap (sg X s)) M U' U _ hx1 hU2).2 g0
  have g2 := (_root_.PositivityTheory.Xgf.hodge_gram_invariant_pullback E H _ _ Xo.univ.t X.t _ X.m (spMap s) (under (spMap s ≫ X.y)) M U' V _ hx2 hV2).1 g1
  refine ⟨fun q => ?_, g2⟩
  exact (tan_iff X.m hx2 (U' q) (V q) (hV2 q)).1
    ((tan_iff X.m' hx1 (U' q) (U q) (hU2 q)).2 (hUt q (one_tangent X b (aq q))))

theorem mat_id {n M : ℕ} {I : Type} [Fintype I] [DecidableEq I] (e : Fin M ≃ Fin n × I) (x : I → ℂ)
    (G : Fin n × I → Fin n × I → ℂ) (A : Matrix (Fin n) (Fin M) ℂ)
    (hA : ∀ k q, A k q = if (e q).1 = k then x (e q).2 else 0) (k k' : Fin n) :
    (A * Matrix.of (fun q q' => G (e q) (e q')) * Aᴴ) k k' =
      ∑ m, ∑ m', x m * G (k, m) (k', m') * starRingEnd ℂ (x m') := by
  have hl : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, A k q * F q = ∑ m, x m * F' (k, m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  have hr : ∀ (k : Fin n) (F : Fin M → ℂ) (F' : Fin n × I → ℂ), (∀ q, F q = F' (e q)) →
      ∑ q, F q * star (A k q) = ∑ m, F' (k, m) * starRingEnd ℂ (x m) := fun k F F' hF => by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp [hA, hF]
    · intro b _ hb
      simp [hA, hb]
    · simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [hr k' _ (fun p' => ∑ m, x m * G (k, m) p') (fun q' => hl k _ (fun p => G p (e q')) fun q => rfl)]
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.Fl.GInf

namespace GlobalTheory.CompanionTheory.Ar.Fl.GInf

theorem hodgeGram_cmVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (n : ℕ) (a : Fin n → PureType.lat hP (sgnRt H b)) (v : Vecs X.y n) (s : X.K →+* ℂ) (y' : Sp ℂ ⟶ Xo.XF c) (v' : Vecs y' n) (r : ℝ), τ (H.rt : E) = sgnRt H b → (∀ k, X.IsCMVec b τ (a k) (v k)) → y' = spMap s ≫ X.y → (∀ k, (v' k).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap s) ≫ (v k).left) → IsLieNormSq (Z b).C.P (Z b).C.v ((s.comp (IntermediateField.inclusion (X.hM b)).toRingHom).comp (algebraMap (𝓞 (Z b).M) (Z b).M)) r → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y') v' (Matrix.of fun k k' => r * ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k'))))) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ n a v s y' v' r hτ hv hy hv' hr
  classical
  subst hy
  have hx2 : under (spMap s ≫ X.y) = spMap s ≫ under X.y := Category.assoc _ _ _
  let e0 : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFin _).symm
  let e : Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) ≃
      Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e0)
  choose nk ek uk h1 h2 using hv
  let W₂ : Fin n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (epsAt (under X.y) ⟶ Xo.univ.t.G) :=
    fun k m => uk k ((ek k).symm m)
  have hW₂ : ∀ k m, X.IsImage b (RingOfIntegers.basis E m • a k) (W₂ k m) := fun k m => by
    have := h1 k ((ek k).symm m)
    rwa [Equiv.apply_symm_apply] at this
  have hVex := fun q => exists_bc (G := Xo.univ.t.G) s (under X.y) hx2 (W₂ (e q).1 (e q).2)
  choose V hV using hVex
  obtain ⟨ht, hg⟩ := gram_family X b τ hτ s r hr (fun q => RingOfIntegers.basis E (e q).2 • a (e q).1)
    (fun q => W₂ (e q).1 (e q).2) (fun q => hW₂ _ _) V hV
  let x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ := fun m => s (X.β (tauE c τ (HT.dualInt E m)))
  let A : Matrix (Fin n) (Fin (n * Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))) ℂ :=
    Matrix.of fun k q => if (e q).1 = k then x (e q).2 else 0
  have hcomb : ∀ k, Fl.IsComb (A k) V (v' k) := fun k => by
    have b1 := isComb_bc s (under X.y) hx2 _ (uk k) (v k) (fun j => V (e.symm (k, ek k j))) (v' k)
      (fun j => by
        rw [hV]
        simp only [Equiv.apply_symm_apply, W₂, Equiv.symm_apply_apply]) (hv' k) (h2 k)
    refine isComb_pad (A k) V (fun j => e.symm (k, ek k j)) (fun j j' hj => ?_) (fun j => ?_) (fun _ => rfl)
      (fun q hq => ?_) ht b1
    · have := e.symm.injective hj
      exact (ek k).injective (Prod.ext_iff.1 this).2
    · simp [A, x]
    · by_contra hne
      have hk : (e q).1 = k := by
        by_contra hk
        exact hne (by simp [A, hk])
      refine hq ⟨(ek k).symm (e q).2, ?_⟩
      simp only [Equiv.apply_symm_apply]
      rw [← hk]
      exact e.symm_apply_apply q
  have g3 := _root_.PositivityTheory.Xgf.hodge_gram_linear_combination _ _ _ _ _ _ V v' _ A ht hg hcomb
  convert g3 using 1
  ext k k'
  have m1 := mat_id e x (fun p p' => (r : ℂ) * kap X τ s (X.h b
    ((RingOfIntegers.basis E p.2 • a p.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La)
    ((RingOfIntegers.basis E p'.2 • a p'.1 : PureType.lat hP (sgnRt H b)) : (FU.Di i).La))) A (fun _ _ => rfl) k k'
  have m2 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component E H (FU.Di i) (X.ε b) (X.h b) (s.comp (X.β.comp (tauE c τ))) (kap X τ s) _ e0 (a k) (a k')
    (X.kform b) rfl
  dsimp only at m1
  have m3 : ∑ m, ∑ m', x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m') =
      ((X.ε b : ℤ) : ℂ) * s (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (a k) (a k')))) := by
    refine Eq.trans ?_ m2
    rw [← Equiv.sum_comp e0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e0]
    rfl
  refine Eq.trans ?_ m1.symm
  rw [Matrix.of_apply, _root_.mul_assoc, ← m3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  show (r : ℂ) * (x m * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La))) * starRingEnd ℂ (x m')) =
    x m * ((r : ℂ) * kap X τ s (X.h b (RingOfIntegers.basis E m • (a k : (FU.Di i).La))
      (RingOfIntegers.basis E m' • (a k' : (FU.Di i).La)))) * starRingEnd ℂ (x m')
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.GInf
