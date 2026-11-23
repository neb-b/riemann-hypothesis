module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelTheta

theorem series_eq_unit_mul_theta : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  intro hL hTX E _ _ _ H D C _ _ _ _ _ o M N' ν' m hm p q v hpz hq hv
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun i =>
    Over.homMk ((o.I.ev (m ^ 2) i).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      simp)
  have key := hTX M.W (IsLocalRing.maximalIdeal M.W) M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm
    D.La p q x (fun i => hpz i (x i) rfl) hq
  have hm0 : (m : C) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
  have hmu : IsUnit ((m : ℕ) : Γ(Sp C, ⊤)) := by
    have h1 : ((m : ℕ) : Γ(Sp C, ⊤)) = fnOf (m : C) := (map_natCast _ m).symm
    rw [h1]
    exact (IsUnit.mk0 _ hm0).map _
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have htors : ∀ i, o.I.ev (m ^ 2) i ^ (m ^ 2) = 1 := fun i => (o.I.onto (m ^ 2) hm2 _).2 ⟨i, rfl⟩
  have : Subsingleton (TFK (R := M.W) C).left := by
    change Subsingleton (PrimeSpectrum C)
    exact ⟨fun a b => PrimeSpectrum.ext (by
      have := a.isPrime
      have := b.isPrime
      rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])⟩
  have : Nonempty (TFK (R := M.W) C).left := by
    change Nonempty (PrimeSpectrum C)
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  have c1 := (GlobalTheory.CoordSep.isThetaPt_iff (T := TFK (R := M.W) C) hm hmu x _).1 key
  have hτ : 𝟙 (Sp C) ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := by simp
  have hβ : 𝟙 (Sp C) ≫ Over.Hom.left (𝟙 (TFK (R := M.W) C)) = 𝟙 (Sp C) := by simp
  have hx : ∀ i, 𝟙 (Sp C) ≫ (x i).left = (o.I.ev (m ^ 2) i).left ≫ M.φ := fun i => Category.id_comp _
  have hz := GlobalTheory.ThetaPtMove.over_one (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) M.cart (𝟙 (Sp C)) hτ
  have hg : ∀ th₀, IsGenSec M.P.A.A M.P.A.L 1 th₀ →
      IsGenSec M.P.A.A M.P.A.L 1 (VVRank.pullS M.P.A.A 1 (𝟙 (TFK (R := M.W) C)) th₀) :=
    fun th h => GlobalTheory.ThetaCoord.isGenSec_pullS M.P.A.isLB (𝟙 _) (𝟙 _) (by simp) h
  have hσ : IsIso (𝟙 (Sp C) : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left) := IsIso.id (Sp C)
  have c2 := GlobalTheory.FullExtend.isCoordPt_move (S := Sp (FractionRing M.W)) (S' := Sp C) (f := jFK (R := M.W) C)
    (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) (𝟙 (Sp C)) (P₀ := M.P.A) (P := o.P) (φ := M.φ) M.cart M.lb
    (B := TFK (R := M.W) C) (𝟙 (Sp C)) (𝟙 _) hβ hτ hg (k := m) (I := D.La) (x := o.I.ev (m ^ 2)) (x₀ := x) hx htors
    (z := 1) (z₀ := 1) hz (v₀ := fun i => fnOf (N'.tx m (q i))) c1
  have e1 : ∀ y : Γ(Sp C, ⊤), (𝟙 (Sp C) : Sp C ⟶ Sp C).appTop.hom y = y := fun y => by simp
  simp only [e1] at c2
  obtain ⟨-, huniq, hthc, hsep⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate hL C (Sp C) o.P (𝟙 (Sp C)) m hm hm0
    D.La (o.I.ev (m ^ 2)) htors
  have hv1 : IsCoordPt o.P m (o.I.ev (m ^ 2)) 1 (fun i => fnOf (v i)) := (hthc v).1 hv
  obtain ⟨c, hc⟩ := (huniq 1 v (fun i => N'.tx m (q i)) hv1).1 c2
  refine ⟨⟨c, fun i => ?_⟩, fun h3 => ?_⟩
  · have := congrFun hc i
    simpa using this
  · have hall : ∀ y : Over.mk (𝟙 (Sp C)) ⟶ o.P.A, y ^ m ^ 2 = 1 → ∃ i, o.I.ev (m ^ 2) i = y :=
      fun y hy => (o.I.onto (m ^ 2) hm2 y).1 hy
    exact (hsep h3 hall 1 1 v hv1 hv1).2

end GlobalTheory.ModelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianValueTableMapsUnderBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.TabMap
open GlobalTheory.FrameGen GlobalTheory.ConstFam GlobalTheory.FrameMove GlobalTheory.OneBasis.Calc

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h a, gs_eq r z _ h, gs_eq q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r _ z h _).symm

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem exists_ptHom (gp : IsGrpPullback A' A f φ) (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ β : (T ⟶ A) →* (T' ⟶ A'), ∀ x, (β x).left ≫ φ = h ≫ x.left := by
  let u : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h (by simpa using hh)
  let b : (T ⟶ A) → (T' ⟶ A') := fun x =>
    Over.homMk (gp.1.lift (h ≫ x.left) T'.hom (by rw [Category.assoc, Over.w, hh])) (gp.1.lift_snd _ _ _)
  have hb : ∀ x, (b x).left ≫ φ = h ≫ x.left := fun x => gp.1.lift_fst _ _ _
  have key : ∀ x y : T' ⟶ A', x.left ≫ φ = y.left ≫ φ → x = y := fun x y hxy => by
    ext1
    exact gp.1.hom_ext hxy ((Over.w x).trans (Over.w y).symm)
  refine ⟨MonoidHom.mk' b (fun x y => key _ _ ?_), hb⟩
  have hu : ∀ z : T ⟶ A, (u ≫ z).left = (b z).left ≫ φ := fun z => by
    rw [hb]
    rfl
  rw [← gp.2 T' (b x) (b y) (u ≫ x) (u ≫ y) (hu x) (hu y), hb, ← MonObj.comp_mul]
  rfl


omit [GrpObj A] in
theorem sval_all {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)} {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
    have := hJ (r ≫ ψ)
    simpa using this
  have H1 := H (r z) (fun ψ => J (r ≫ ψ)) hJ'
  rw [sval_of s q (r z) _ (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => rfl),
    val_of e (𝟙 _) (r z) _ (fun _ => J (r ≫ p)) (fun _ => by simp)] at H1
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) (r ≫ q)
  have hm' := hJ.mem (fun _ : Fin 1 => p) r
  rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by simp),
    val_of e r z J (fun _ => J (r ≫ p)) (fun _ => rfl)]
  simp only [Category.assoc] at hm
  refine (gs_comp r q z _ hm _).trans ?_
  erw [H1]
  rw [map_mul]
  congr 1
  · have := gs_comp r (𝟙 _) z ⊤ trivial c
    simpa using this.symm
  · erw [← gs_unit r z _ hm', ← gs_unit (𝟙 _) (r z) _ (by simpa using hm')]
    have := gs_comp r (𝟙 _) z (L.wchart (fun _ => p) fun _ => J (r ≫ p)) hm' (e.s fun _ => J (r ≫ p)).val
    rw [Category.comp_id] at this
    exact this.symm
end

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem cmb_move (hφ : φ ≫ P.A.hom = P'.A.hom ≫ f) (hh : h ≫ T.hom = T'.hom ≫ f) {k n : ℕ}
    {b : Fin n → LB.Sec (LPow P.A P.L (k : ℤ) T)} {c : Fin n → Γ(T.left, ⊤)} {t : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow P'.A P'.L (k : ℤ) T')} {t' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')}
    (H : ∀ j, t.f j = ∑ i, liftFun P.A _ (c i) * (b i).f j) (hb : ∀ i, Thru w k h (b i) (b' i)) (ht : Thru w k h t t') :
    ∀ j, t'.f j = ∑ i, liftFun P'.A _ (h.appTop.hom (c i)) * (b' i).f j := by
  have hl : Lin P.A P.L k (𝟙 T) b c t := by
    intro z J hJ
    have e := (cmb_iff P.isLB b c t).1 H _ (𝟙 _) z J hJ
    have hw : ((𝟙 T) ▷ P.A).left = 𝟙 _ := by simp
    rw [hw]
    refine e.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    rw [Category.id_comp, gs_eq (fst T P.A).left z ⊤ trivial]
    rfl
  exact cmb_of_lin hφ P.isLB P'.isLB hh (h := 𝟙 T) (p := h) (by simp) hl hb ht

theorem frame_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) {x : T ⟶ P.A} {x' : T' ⟶ P'.A}
    (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} {e} (H : IsTorsFrame P ρ n x e) :
    ∃ e', IsTorsFrame P' ρ' n x' e' ∧ ∀ (k : ℕ) (s : LB.Sec (LPow P.A P.L (k : ℤ) T))
      (s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')) (c : Γ(T.left, ⊤)), Thru w k h s s' →
      (∀ z J, Good P.L z J → sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (k : ℤ)) s
        (ptSecT P.A x).left z J = gs (𝟙 _) z ⊤ c * (val (powFrame P.A P.L x e k) (𝟙 _) z J).val) →
      ∀ z J, Good P'.L z J → sval (φ := fun _ : Fin 1 => (snd T' P'.A).left) (ε := fun _ => (k : ℤ)) s'
        (ptSecT P'.A x').left z J = gs h z ⊤ c * (val (powFrame P'.A P'.L x' e' k) (𝟙 _) z J).val := by
  obtain ⟨gp, hw, -, hpm⟩ := R
  obtain ⟨e', he', hv⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x'.left) (φ := fun _ : Fin 1 => x.left) (h := h)
    (ε := fun _ => 1) hw P.isLB P'.isLB (fun _ => hx) e H.2.1
  have ht : ∀ (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val e h z J = wVal w z J J' x'.left * val e' (𝟙 _) z J' := by
    intro z J J' hJ hJ'
    have := hv _ (𝟙 _) z J J' hJ hJ'
    simpa using this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval ρ (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval ρ' r z J' := by
    intro Z r z J J' hJ hJ'
    have := pmaps_val (fun _ => PolBaseChange.eSec_comm gp) hpm r hJ hJ'
    simpa using this
  refine ⟨e', isTorsFrame_move gp hw hr hx H he' ht, ?_⟩
  intro k s s' c hs hval z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' P.isLB z
  have pf : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (fst U A₀).left = 𝟙 _ :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have ps : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (snd U A₀).left = y.left :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_snd]
  have c1 : (h ≫ (ptSecT P.A x).left) ≫ (fst T P.A).left = (ptSecT P'.A x').left ≫ (fst T' P'.A).left ≫ h := by
    rw [Category.assoc, pf, ← Category.assoc, pf, Category.comp_id, Category.id_comp]
  have c2 : (h ≫ (ptSecT P.A x).left) ≫ (snd T P.A).left = (ptSecT P'.A x').left ≫ (snd T' P'.A).left ≫ φ := by
    rw [Category.assoc, ps, ← Category.assoc, ps, hx]
  have h1 := hs _ (ptSecT P'.A x').left (h ≫ (ptSecT P.A x).left) c1 c2 z J J' hJ hJ'
  have h2 := sval_all hval h z hJ
  rw [ps] at h1
  rw [h1, val_powFrame, ht z J J' hJ hJ'] at h2
  rw [val_powFrame]
  simp only [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val] at h2 ⊢
  apply ((wVal w z J J' x'.left).isUnit.pow k).mul_left_cancel
  rw [h2]
  ring
end

theorem tab_map : LL → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m r : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (τ : Fin r → SecA A F (m ^ 2)) (τ' : Fin r → SecA A' F' (m ^ 2)), Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → (∀ i, Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) (τ i) (τ' i)) → Tab.Map σ (tab ρ m th τ) (tab ρ' m th' τ') := by
  intro hLL R R' _ _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ _ _ σ hσ m r th th' τ τ' hth hτ
  have gp := hR.1
  have hw := hR.2.1
  have hφ : ψ ≫ A.A.hom = A'.A.hom ≫ spMap gam := gp.1.w
  have hh : spMap σ ≫ (TFK (R := R) F).hom = (TFK (R := R') F').hom ≫ spMap gam := by
    show spMap σ ≫ spMap (algebraMap (FractionRing R) F) = spMap (algebraMap (FractionRing R') F') ≫ spMap gam
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext hσ
  obtain ⟨β, hβ⟩ := exists_ptHom (T := TFK (R := R) F) (T' := TFK (R := R') F') (h := spMap σ) gp hh
  have thru : ∀ (k : ℕ) (s : SecA A F k), ∃ s' : SecA A' F' k,
      Thru ω k (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) s s' :=
    fun k s => (existsUnique_thru hφ hw A.isLB A'.isLB hh s).exists
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro k y₁ hk hy₁
    obtain ⟨y, rfl⟩ : ∃ y : TFK (R := R') F' ⟶ A'.A, y = y₁ := ⟨y₁, rfl⟩
    have hy : y ^ k = 1 := hy₁
    have hk0 : (k : F) ≠ 0 := by
      rw [← map_natCast (algebraMap (FractionRing R) F), ← map_natCast (algebraMap R (FractionRing R))]
      intro h0
      rw [map_eq_zero_iff _ (algebraMap (FractionRing R) F).injective,
        map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h0
      exact (Nat.cast_ne_zero.2 (by omega : k ≠ 0)) h0
    have hz : (y.left ≫ ψ) ≫ A.A.hom = spMap σ ≫ (TFK (R := R) F).hom := by
      rw [Category.assoc, hφ, ← Category.assoc, Over.w, hh]
    let zt : Over.mk (spMap σ ≫ (TFK (R := R) F).hom) ⟶ A.A := Over.homMk (y.left ≫ ψ) hz
    have hzy : y.left ≫ ψ = 𝟙 (TFK (R := R') F').left ≫ zt.left := by simp [zt]
    have hzk : zt ^ k = 1 := by
      have e1 := pow_comm gp hzy k
      have e0 := pow_comm gp hzy 0
      rw [hy] at e1
      simp only [pow_zero] at e0
      ext1
      have := e1.symm.trans e0
      erw [Category.id_comp, Category.id_comp] at this
      exact this
    obtain ⟨x, hxk, hxz⟩ := (GlobalTheory.torsion_points_field_extension hLL.1 _ A F F' σ (TFK (R := R) F).hom).2 k zt hk0 hzk
    refine ⟨x, hxk, ?_⟩
    apply Over.OverMorphism.ext
    apply gp.1.hom_ext
    · refine (hβ x).trans ?_
      have := congrArg CommaMorphism.left hxz
      simpa [zt] using this
    · exact (Over.w (β x)).trans (Over.w y).symm
  · rintro x a ⟨hx, t, c, hc, hcmb⟩
    obtain ⟨t', ht'⟩ := thru _ t
    refine ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t', σ c,
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ m th th' x (β x) t t' c (hβ x) hth ht' hc, ?_⟩
    intro j
    rw [cmb_move hφ hh hcmb hτ ht' j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (spMap σ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) =
      (Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (σ (a i)) from appTop_fnR σ (a i)]
    rfl
  · rintro k x c ⟨hx, t, hc⟩
    obtain ⟨t', ht'⟩ := thru _ t
    exact ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t',
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ k th th' x (β x) t t' c (hβ x) hth ht' hc⟩
  · rintro k x l ⟨e, he, hv⟩
    obtain ⟨e', he', hmv⟩ := frame_move hR (hβ x) he
    refine ⟨e', he', fun j z J' hJ' => ?_⟩
    have := hmv (m ^ 2) (τ j) (τ' j) (fnR (l j)) (hτ j) (hv j) z J' hJ'
    erw [gs_spMap] at this
    exact this

end GlobalTheory.OneBasis.TabMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleLocalBase

theorem relAmple_baseChange {S S' : Scheme.{0}} [IsAffine S] {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f)
    (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  obtain ⟨w, hw⟩ := hw
  exact relAmple_pull h hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hA

theorem relAmple_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  intro R _ _ _ B M hF hP hM R₀ _ _ g hg Y₀ b hb N₀ hN₀ hiso hA
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre R B M hF hP hM _ (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

end GlobalTheory.AmpleLocalBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesConv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefVal

theorem summable_coef : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u _ k hk s g w hw
  have hTW : TwistBCSpanStatement := twistBCSpan_of (GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  obtain ⟨v, hvn⟩ := PadicVal.exists_addValuation _ h0 h1
  have hv : ValOver ϖ (PadicAlgCl p) v := fun c n hc => by
    have e := PsiForm.norm_of_hasVal u.norm_le hϖ hc
    obtain ⟨q, hq, hq'⟩ := hvn (algebraMap _ _ c) (norm_pos_iff.1 (by rw [e]; exact Real.exp_pos _))
    rw [e, Real.log_exp, neg_mul, neg_neg, mul_comm, mul_left_inj' (Real.log_neg h0 h1).ne] at hq'
    have : q = n := by exact_mod_cast hq'.symm
    rw [hq, this]
  have ht : Filter.Tendsto (fun χ => coef s g w χ) Filter.cofinite (nhds 0) := by
    refine PadicVal.tendsto_of_null h0 h1 hvn fun q => ?_
    obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q :=
      WithTop.coe_lt_coe.1 ((le_v_coef hw (hr χ) (hl χ) hω).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith
  obtain ⟨T, hT⟩ := CoefField.exists_finset hLL.1.globalFns hk s g hw fun α => by
    obtain ⟨r, n, a, σ, σF, hσ, -, hsum⟩ := exists_vge hϖ hv hTW hk (s.s α)
    exact ⟨n, a, σ, σF, hσ, hsum⟩
  obtain ⟨-, -, -, K₀, hK₀, hK⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hm : ∀ χ, coef s g w χ ∈ K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p)) :=
    hT (K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))).toSubfield
      (fun a => (le_sup_left : K₀ ≤ _) (show _ ∈ (K₀ : Set (PadicAlgCl p)) from hK ▸ ⟨a, rfl⟩))
      (fun t h => (le_sup_right : _ ≤ K₀ ⊔ _) (IntermediateField.subset_adjoin _ _ h))
  exact ⟨PadicVal.summable_of_mem _ hm ht, ht, _, inferInstance, hm⟩

end GlobalTheory.ZH.SeriesConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsMatchOfLevelGeFour
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait.LevelFour

theorem exists_image {C : Type} [Field C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, J.Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, hg⟩
  have a := hp k
  rw [N.mem_QT.1 p.2] at a
  exact (h₁ _).unique a (h₃ _)

theorem ev_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2)
    {g : N.Gt} {g' : N'.Gt} (hg : J.Rel g g') :
    N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun χ => (H χ).2 g g' hg

theorem labels_of_four_le : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  intro hL hE hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT hR n hn h3 hl k hk
    x p q' p' z hp e₁ e₂ hq hz
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  choose pt hpt using fun i : D.La => (existsUnique_twRel A.be u (r (n ^ 2)) (hr.pow hn2) (A.q (n ^ 2) i)).exists
  choose qt hq₁ hq₂ using fun i => exists_image J (pt i)
  choose pp hpp using fun i => (B.2.2.2.2 (n ^ 2)).2.1 (qt i)
  have hA : ∀ i, M.P.ToA C (n ^ 2) (pp i) (e (o.I.ev (n ^ 2) i)) := fun i =>
    hl i (pt i) (qt i) (pp i) _ (hpt i) (hq₁ i) (hq₂ i) (hpp i) (he _)
  obtain ⟨F, hF, -⟩ := hT C k (by omega)
  obtain ⟨y, hy⟩ := e.surjective (F p')
  have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' n hn D.La pp qt _ hA hpp
    k hk p' q' (F p') ((hF _ _).2 rfl) hq
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have ht : ∀ i, o.I.ev (n ^ 2) i ^ (n ^ 2) = 1 := fun i => (o.I.onto _ hn2 _).2 ⟨i, rfl⟩
  have Q₁ : IsCoordPt o.P n (T := baseOver (Sp C)) (o.I.ev (n ^ 2)) y fun i => fnOf (N'.ev n (qt i) q'.1.2) :=
    FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (he _)) ht (z := y)
      ((Category.id_comp _).trans ((congrArg (fun w => w.left) hy).symm.trans (he _))) Q
  have Q₂ := ((hR.2.2.2 n hn pt hpt).2.2 k (by omega) x p hp).2
  obtain ⟨-, s₂, -, s₄⟩ := CoordSep.coord_exists_unique_separate hL.1 C (Sp C) o.P (𝟙 _) n hn
    (Nat.cast_ne_zero.2 hn.pos.ne') D.La (o.I.ev (n ^ 2)) ht
  have Q₃ := (s₂ _ _ (fun i => N'.ev n (qt i) q'.1.2) Q₂).2
    ⟨J.lam * J.h p.1.2.b ^ (n ^ 2), funext fun i => ev_iso J hn (hq₁ i) (hq₂ i) e₂⟩
  obtain rfl := (s₄ h3 (fun w hw => (o.I.onto _ hn2 w).1 hw) _ _ _ Q₃ Q₁).1
  exact (hF _ _).2 ((Over.OverMorphism.ext (hz.trans (he _).symm)).trans hy)

end GlobalTheory.Ex.Trait.LevelFour
end

