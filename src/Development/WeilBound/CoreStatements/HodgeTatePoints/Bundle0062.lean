module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPar
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {S : Scheme.{0}}
  (t : SAB H S) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ S)

structure IsParam (n : ℕ) (ev : D.La → (Over.mk ξ ⟶ t.G)) (ζ₀ : Ωˣ) : Prop where
  prim : IsPrimitiveRoot ζ₀ n
  add : ∀ a b, ev (a + b) = ev a * ev b
  lin : ∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ t.act.act c
  ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b
  onto : ∀ g, g ^ n = 1 ↔ ∃ a, ev a = g
  weil : ∀ (a b : D.La) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
    (xk gk : Over.mk (spMap i ≫ ξ) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ (ev a).left →
      gk.left = spMap i ≫ (ev b).left →
      (Out.WeilIs t.G t.PP.L n xk gk (unitOn c) ↔ (c : k) = i ((ζ₀ ^ D.EF a b : Ωˣ) : Ω))
  tate : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k),
    ∃ I : TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left

def bcPt {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') : Over.mk ξ' ⟶ Over.mk ξ :=
  Over.homMk (spMap f) h

theorem bcPt_left {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') {G : Over S}
    (g : Over.mk ξ ⟶ G) : (bcPt ξ f ξ' h ≫ g).left = spMap f ≫ g.left := rfl

theorem bcPt_cancel {K : Type} [Field K] (f : Ω →+* K) (ξ' : Sp K ⟶ S) (h : spMap f ≫ ξ = ξ') {G : Over S}
    {g g' : Over.mk ξ ⟶ G} (e : bcPt ξ f ξ' h ≫ g = bcPt ξ f ξ' h ≫ g') : g = g' := by
  have := HTTie.epi_spMap f
  have e' : spMap f ≫ g.left = spMap f ≫ g'.left := congrArg CommaMorphism.left e
  exact Over.OverMorphism.ext ((cancel_epi _).1 e')

theorem exists_isParam (h578 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.HT.level_parametrisation) [CharZero Ω] (n : ℕ) (hn : 1 ≤ n) (hpq : 0 < D.p + D.q)
    (hprop : IsProper (pullback.snd t.G.hom ξ)) (hfull : FullTorsion t.G ξ n)
    (hT : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k),
      Nonempty (TateIso D k (Over.mk (spMap f ≫ ξ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))) :
    ∃ ev ζ₀, IsParam D t ξ n ev ζ₀ := by
  obtain ⟨ev, ζ₀, hζ, hI⟩ := h578 E H D S t Ω ξ n hn hpq hprop hfull hT
  obtain ⟨I, -, hIe⟩ := hI (AlgebraicClosure Ω) (algebraMap Ω _)
  let ψ := bcPt ξ (algebraMap Ω (AlgebraicClosure Ω)) _ rfl
  have hψ : ∀ a, I.ev n a = ψ ≫ ev a := fun a => Over.OverMorphism.ext (hIe a)
  have can : ∀ {g g' : Over.mk ξ ⟶ t.G}, ψ ≫ g = ψ ≫ g' → g = g' := fun e => bcPt_cancel ξ _ _ rfl e
  refine ⟨ev, ζ₀, hζ, fun a b => can ?_, fun c a => can ?_, fun a => ?_, fun g => ?_, ?_, hI⟩
  · rw [comp_mul, ← hψ, ← hψ, ← hψ, I.add]
  · rw [← Category.assoc, ← hψ, ← hψ, I.lin]
  · rw [← I.ker n hn a, hψ]
    exact ⟨fun h => by rw [h, MonObj.comp_one], fun h => can (by rw [h, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto n hn (ψ ≫ g)).1 (by rw [← HTTie.comp_pow', hg, MonObj.comp_one])
      exact ⟨a, can (by rw [← hψ, ha])⟩
    · rintro ⟨a, rfl⟩
      refine can ?_
      rw [HTTie.comp_pow', ← hψ, MonObj.comp_one]
      exact (I.onto n hn _).2 ⟨a, rfl⟩
  · intro a b k _ _ i xk gk c hx hg
    obtain ⟨I', hz, hI'⟩ := hI k i
    obtain rfl : xk = I'.ev n a := Over.OverMorphism.ext (hx.trans (hI' a).symm)
    obtain rfl : gk = I'.ev n b := Over.OverMorphism.ext (hg.trans (hI' b).symm)
    have h0 := I'.isom n hn a b
    have hv : ((I'.ζ n ^ D.EF a b : kˣ) : k) = i ((ζ₀ ^ D.EF a b : Ωˣ) : Ω) := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hz]
    constructor
    · intro h
      rw [GlobalTheory.weilIs_unique_fieldPoint S t.G t.PP.L t.PP.isLB k _ n _ _ _ _ h h0, hv]
    · intro h
      obtain rfl : c = I'.ζ n ^ D.EF a b := Units.ext (h.trans hv.symm)
      exact h0

theorem IsParam.tate' {n : ℕ} {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ n ev ζ₀)
    (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k) (ξ' : Sp k ⟶ S) (h : spMap f ≫ ξ = ξ') :
    ∃ I : TateIso D k (Over.mk ξ' ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ n : k) = f ζ₀ ∧ ∀ a, (I.ev n a).left = spMap f ≫ (ev a).left := by
  subst h
  exact hev.tate k f

theorem isProper_of_iso {G S Y Z : Scheme.{0}} (f : G ⟶ S) (h : Y ⟶ S) (g : Z ⟶ Y) (h' : Z ⟶ S) (e : g ≫ h = h')
    [IsProper (pullback.snd f h)] : IsProper (pullback.snd f h') := by
  subst e
  have hp : IsPullback (pullback.lift (pullback.fst f (g ≫ h)) (pullback.snd f (g ≫ h) ≫ g)
      (by rw [pullback.condition, Category.assoc])) (pullback.snd f (g ≫ h)) (pullback.snd f h) g := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f h)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback f (g ≫ h)
  exact MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance

theorem exists_chartGroup (h450 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion) (p m : ℕ) [Fact p.Prime]
    {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ (p ^ m) ev ζ₀)
    (hprop : IsProper (pullback.snd t.G.hom ξ)) (hfull : FullTorsion t.G ξ (p ^ m))
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CharZero A] (x : Sp A ⟶ S)
    (κ : FractionRing A ≃+* Ω) (hx : spMap (κ.toRingHom.comp (algebraMap A (FractionRing A))) ≫ x = ξ) :
    ∃ (Γ : BT.QFGroup A (LevGrp D.La p m)) (i : Γ.G.left ⟶ t.G.left), Γ.IsTorsionAlong t.G x (p ^ m) i ∧
      (∀ a, spMap κ.toRingHom ≫ (Γ.pt (lev p m a)).left ≫ i = (ev a).left) ∧
      (∀ (c : 𝓞 E) a, (Γ.pt (lev p m (c • a))).left ≫ i = (Γ.pt (lev p m a)).left ≫ i ≫ (t.act.act c).left) ∧
      IsProper (pullback.snd t.G.hom ((BT.genPt A).hom ≫ x)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing A →+* k),
        ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt A).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a)
            (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
          (I.ζ (p ^ m) : k) = f (κ.symm (ζ₀ : Ω)) ∧
            ∀ a, (I.ev (p ^ m) a).left = spMap f ≫ (Γ.pt (lev p m a)).left ≫ i := by
  have hpos : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos _
  have hq : spMap κ.symm.toRingHom ≫ ξ = (BT.genPt A).hom ≫ x := by
    rw [← hx, ← Category.assoc, ← HTTie.spec_comp]
    congr 2
    ext a
    simp
  have hκκ : spMap κ.toRingHom ≫ spMap κ.symm.toRingHom = 𝟙 _ := by
    rw [← HTTie.spec_comp]
    have : κ.toRingHom.comp κ.symm.toRingHom = RingHom.id Ω := by ext a; simp
    rw [this]
    exact Spec.map_id _
  let ψ := bcPt ξ κ.symm.toRingHom _ hq
  have ev0 : ev 0 = 1 := (hev.ker 0).2 ⟨0, by simp⟩
  let φ : Multiplicative D.La →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G) :=
    { toFun := fun a => ψ ≫ ev a.toAdd
      map_one' := by
        show ψ ≫ ev 0 = 1
        rw [ev0, MonObj.comp_one]
      map_mul' := fun a b => by
        show ψ ≫ ev (a.toAdd + b.toAdd) = _
        rw [hev.add, comp_mul] }
  let π₀ : Multiplicative D.La →* LevGrp D.La p m :=
    (LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La))).mkQ.toAddMonoidHom.toMultiplicative
  have hπ₀ : ∀ a, π₀ (Multiplicative.ofAdd a) = lev p m a := fun a => rfl
  have hsurj : ∀ s : LevGrp D.La p m, ∃ a, lev p m a = s := fun s => by
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ s.toAdd
    exact ⟨a, congrArg Multiplicative.ofAdd ha⟩
  have hlev : ∀ a : D.La, lev p m a = 1 ↔ ∃ b, a = p ^ m • b := fun a => by
    have : lev p m a = 1 ↔ a ∈ LinearMap.range ((p ^ m) • (LinearMap.id : D.La →ₗ[ℤ] D.La)) :=
      Submodule.Quotient.mk_eq_zero _
    rw [this]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hs₀ : Function.Surjective π₀ := fun s => by
    obtain ⟨a, ha⟩ := hsurj s
    exact ⟨Multiplicative.ofAdd a, ha⟩
  let τ : LevGrp D.La p m →* (Over.mk ((BT.genPt A).hom ≫ x) ⟶ t.G) :=
    π₀.liftOfRightInverse (Function.surjInv hs₀) (Function.rightInverse_surjInv hs₀)
      ⟨φ, fun z hz => by
        have h1 : lev p m z.toAdd = 1 := hz
        show ψ ≫ ev z.toAdd = 1
        rw [(hev.ker _).2 ((hlev _).1 h1), MonObj.comp_one]⟩
  have hτ : ∀ a, τ (lev p m a) = ψ ≫ ev a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (Multiplicative.ofAdd a)
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    obtain ⟨a, rfl⟩ := hsurj s
    rw [hτ] at hs
    exact (hlev a).2 ((hev.ker a).1 (bcPt_cancel ξ _ _ hq (hs.trans (MonObj.comp_one _).symm)))
  have htor : ∀ s, τ s ^ (p ^ m) = 1 := fun s => by
    obtain ⟨a, rfl⟩ := hsurj s
    rw [hτ, ← HTTie.comp_pow', (hev.onto _).2 ⟨a, rfl⟩, MonObj.comp_one]
  have hk : ∀ (k : Type) [Field k] (f : FractionRing A →+* k),
      spMap (f.comp κ.symm.toRingHom) ≫ ξ = spMap f ≫ (BT.genPt A).hom ≫ x := fun k _ f => by
    rw [← hq, ← Category.assoc, ← HTTie.spec_comp]
  have hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing A →+* k)
      (g : Over.mk (spMap f ≫ (BT.genPt A).hom ≫ x) ⟶ t.G), g ^ (p ^ m) = 1 →
      ∃ s, g.left = spMap f ≫ (τ s).left := by
    intro k _ _ f g hg
    obtain ⟨I, -, hI⟩ := hev.tate' D t ξ k _ _ (hk k f)
    obtain ⟨a, rfl⟩ := (I.onto _ hpos g).1 hg
    refine ⟨lev p m a, ?_⟩
    rw [hI, hτ, bcPt_left]
    exact (congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)
  obtain ⟨Γ, i, hi, hpt⟩ := h450 A (LevGrp D.La p m) S t.G t.semi x (p ^ m) hpos τ hinj htor hgeo
  have hpt' : ∀ a, (Γ.pt (lev p m a)).left ≫ i = spMap κ.symm.toRingHom ≫ (ev a).left := fun a => by
    rw [hpt, hτ, bcPt_left]
  refine ⟨Γ, i, hi, fun a => ?_, fun c a => ?_, isProper_of_iso _ ξ _ _ hq, fun k _ _ f => ?_⟩
  · rw [hpt', ← Category.assoc, hκκ, Category.id_comp]
  · rw [← Category.assoc, hpt', hpt', hev.lin, Category.assoc]
    rfl
  · obtain ⟨I, hz, hI⟩ := hev.tate' D t ξ k _ _ (hk k f)
    refine ⟨I, hz, fun a => ?_⟩
    rw [hI, hpt']
    exact (congrArg (· ≫ (ev a).left) (HTTie.spec_comp κ.symm.toRingHom f)).trans (Category.assoc _ _ _)

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MiTors
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mi

section Cat
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]


omit [BraidedCategory C] in
theorem isMonHom_of_mul {A B : C} [GrpObj A] [GrpObj B] (j : A ⟶ B)
    (h : ∀ (Y : C) (y z : Y ⟶ A), (y * z) ≫ j = (y ≫ j) * (z ≫ j)) : IsMonHom j := by
  constructor
  · have h1 := h (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ A) ≫ j = 1 := by
      have := h1
      exact (left_eq_mul.1 this)
    simpa [Hom.one_def] using h2
  · have h1 := h (A ⊗ A) (fst A A) (snd A A)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1
    ext <;> simp

theorem isPullback_of_kernel {A B : C} [GrpObj B] [IsCommMonObj B] {N : ℕ} (j : A ⟶ B)
    (inj : ∀ (Y : C) (y z : Y ⟶ A), y ≫ j = z ≫ j → y = z)
    (ker : ∀ (Y : C) (g : Y ⟶ B), g ^ N = 1 ↔ ∃ y : Y ⟶ A, y ≫ j = g) :
    IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] := by
  have hw : j ≫ (𝟙 B) ^ N = toUnit A ≫ η[B] := by
    rw [comp_pow_id, (ker A j).2 ⟨𝟙 _, Category.id_comp _⟩, Hom.one_def]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ((ker _ s.fst).1 ?_).choose) (fun s => ?_) (fun s => ?_)
    (fun s m h1 _ => ?_)⟩⟩
  · rw [← comp_pow_id s.fst, Hom.one_def, ← toUnit_unique s.snd (toUnit _)]
    exact s.condition
  · exact Exists.choose_spec (p := fun y => y ≫ j = s.fst) _
  · exact toUnit_unique _ _
  · apply inj
    rw [h1]
    exact (Exists.choose_spec (p := fun y => y ≫ j = s.fst) _).symm

omit [BraidedCategory C] in
theorem pow_comp {Y A B : C} [GrpObj A] [GrpObj B] (g : Y ⟶ A) (a : A ⟶ B) [IsMonHom a] (n : ℕ) :
    (g ^ n) ≫ a = (g ≫ a) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

end Cat

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem kernel_of_tors (h : Γ.IsTorsionAlong G x N i) :
    ∃ j : Γ.G ⟶ (Over.pullback x).obj G, j.left ≫ pullback.fst G.hom x = i ∧
      IsPullback j (toUnit Γ.G) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hj : (toPull x G g).left ≫ pullback.fst G.hom x = i := toPull_fst x G g
  refine ⟨toPull x G g, hj, isPullback_of_kernel _ (fun Y y z e => h.inj Y y z ?_) (fun Y c => ?_)⟩
  · rw [← hj, ← Category.assoc, ← Category.assoc, ← Over.comp_left, e, Over.comp_left]
  · have h1 : c ^ N = 1 ↔ ofPull x G c ^ N = 1 := by
      have h2 := map_pow (toPullHom x G Y) (ofPull x G c) N
      have h3 : toPullHom x G Y (ofPull x G c) = c := toPull_ofPull x G c
      rw [h3] at h2
      rw [← h2]
      constructor
      · intro e
        rw [← map_one (toPullHom x G Y)] at e
        exact toPull_inj e
      · intro e
        rw [e, map_one]
    rw [h1, h.kernel]
    refine exists_congr fun y => ⟨fun e => hom_ext_pull ?_, fun e => ?_⟩
    · rw [Over.comp_left, Category.assoc, hj, e]; rfl
    · rw [← hj, ← Category.assoc, ← Over.comp_left, e]; rfl

end Tors

theorem kernel_isPullback {Z : Scheme.{0}} {A B D : Over Z} [GrpObj D] {j : A ⟶ B} {q : B ⟶ D}
    (hp : IsPullback j (toUnit A) q η[D]) : IsPullback j.left A.hom q.left (η[D]).left := by
  have hl := hp.map (Over.forget Z)
  have hA : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  rw [← hA]; exact hl

theorem isClosedImmersion_unit {Z : Scheme.{0}} (B : Over Z) [GrpObj B] [IsSeparated B.hom] :
    IsClosedImmersion (η[B]).left := by
  have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
    have : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
    rw [this]; infer_instance
  exact IsClosedImmersion.of_comp _ B.hom

theorem torsion_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hprop
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have : IsProper ((Over.pullback x).obj G).hom := hprop
  have hj : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (kernel_isPullback hp).flip (isClosedImmersion_unit _)
  have : IsProper Γ.G.hom := by rw [← Over.w j]; infer_instance
  have := Γ.quasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem torsion_etale : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h _ hN
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e1 : FormallyUnramified ((𝟙 ((Over.pullback x).obj G)) ^ N).left :=
    GlobalTheory.formallyUnramified_mulA _ ((Over.pullback x).obj G) N hN'
  have : FormallyUnramified Γ.G.hom := MorphismProperty.of_isPullback (kernel_isPullback hp) e1
  have := Γ.flat
  have := Γ.finPres
  exact Etale.of_formallyUnramified_of_flat _

theorem torsion_end : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  intro R _ _ T _ _ Γ S G _ _ x N i h a _
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by rw [← pow_comp, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a', isMonHom_of_mul _ fun Y y z => h.inj Y _ _ ?_, ha'⟩
  let p : (Y ⟶ Γ.G) → (Over.mk (Y.hom ≫ x) ⟶ G) := fun y => Over.homMk (y.left ≫ i) (by
    simp only [Over.mk_hom, Category.assoc, h.isOver]; rw [← Category.assoc, Over.w])
  have hp : ∀ y, (p y).left = y.left ≫ i := fun _ => rfl
  have hpa : ∀ y, (p y ≫ a).left = (y ≫ a').left ≫ i := fun y => by
    rw [Over.comp_left, Over.comp_left, hp, Category.assoc, Category.assoc, ha']
  rw [← h.mul Y _ _ _ _ (hpa y) (hpa z), ← MonObj.mul_comp, Over.comp_left, Over.comp_left,
    h.mul Y _ _ _ _ (hp y) (hp z), Category.assoc, Category.assoc, ha']

end PositivityTheory.HtPt.Mi
end
end

