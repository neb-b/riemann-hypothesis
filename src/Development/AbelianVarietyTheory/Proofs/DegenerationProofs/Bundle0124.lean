module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullExtend

open ThetaPtMove

theorem isCoordPt_move {S S' : Scheme.{0}} {f : S' ⟶ S} {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {z : T ⟶ P.A} {z₀ : T₀ ⟶ P₀.A} (hz : τ ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(T₀.left, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ho, hu, th₀, s₀, α₀, ρ₀, U₀, t₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => z.left) (h := τ) hw hL₀ hL₁
    (fun _ => hz.symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  exact ⟨ho, (map_natCast τ.appTop.hom k) ▸ hu.map τ.appTop.hom, th, s, α, ρ, U, t,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i), fun i => isValueAt_move hp τ hτ hL₀ hL₁ hz vρ (ht i) (h₇ i)⟩

theorem isGenSec_base (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Sp K)) {R : Type} [CommRing R]
    (t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (h : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t ≫ overResι ⊤) th) := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let i : baseOver (Sp K) ⟶ overRes (T := baseOver (Sp K)) ⊤ := Over.homMk (Sp K).topIso.inv
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Scheme.toIso_inv_ι _))
  have hi : overResι (T := baseOver (Sp K)) ⊤ ≫ i = 𝟙 _ := Over.OverMorphism.ext (Sp K).topIso.hom_inv_id
  have h₁ : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (overResι ⊤) th) := fun s => by
    obtain ⟨r, hr⟩ := h (VVRank.pullS P.A 1 i s)
    have e : VVRank.pullM P.A P.L 1 i (SecM.ofSec P.A s) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have := congrArg (VVRank.pullM P.A P.L 1 (overResι ⊤)) e
    rw [VVRank.pullM_comp P.A P.isLB, hi, VVRank.pullM_id P.A P.isLB, LinearMap.map_smulₛₗ] at this
    exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩
  intro s
  obtain ⟨r, hr⟩ := isGenSec_pullS hS p₀ P t _ h₁ s
  have e := VVRank.pullM_comp P.A P.isLB 1 (homAt t) (overResι ⊤) (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e))⟩

theorem isCoordPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre f P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) h.2.1 h.2.2.symm σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (isGenSec_base hS P₀ t) hx hk hz H

theorem prim_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso (L.pull φ) L') {a : G ⟶ G} {a' : G' ⟶ G'}
    (ha : a'.left ≫ φ = φ ≫ a.left) (H : LBIso L (cubeLB G ![𝟙 G, a] L)) : LBIso L' (cubeLB G' ![𝟙 G', a'] L') := by
  have i₁ := pull_isLB hL φ
  have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', a'] (L.pull φ)) := by
    let U := pushPt h.1.w (𝟙 G')
    refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    fin_cases i
    · exact (Category.comp_id _).symm
    · exact Over.OverMorphism.ext (ha.trans (congrArg (· ≫ a.left) (Category.id_comp _).symm))
  obtain ⟨w, hw'⟩ := id hw
  exact LBIso.trans hL' (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ hL' _ _)
    (LBIso.trans hL' i₁ (DVR.linComb_isLB _ i₁ _ _) hw.symm h₁) ⟨_, DVR.linCombIso_isGen w hw' _ _⟩

theorem exists_pointMap (hL : Laws) {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K']
    {f : K →+* K'} {P : PolAV (Sp K)} {P' : PolAV (Sp K')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ) :
    ∃ r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A), (∀ x, (r x).left ≫ φ = spMap f ≫ x.left) ∧
      Function.Injective r ∧ (∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, x ^ n = 1 ∧ r x = y) ∧
      ∀ (n : ℤ) x y (c : Kˣ), WeilIs P.A P.L n x y (unitOn c) →
        WeilIs P'.A P'.L n (r x) (r y) (unitOn (Units.map f.toMonoidHom c)) := by
  have := P'.isAb.comm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h.2.1 (baseOver (Sp K')) _ rfl
  let U : Over.mk ((baseOver (Sp K')).hom ≫ spMap f) ⟶ baseOver (Sp K) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A) := e.symm.toMonoidHom.comp (preHom U)
  have hr : ∀ x, (r x).left ≫ φ = spMap f ≫ x.left := fun x =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (U ≫ x)))
  have inj : Function.Injective r := by
    letI := f.toAlgebra
    haveI : Flat (spMap f) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K K')
    haveI : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap f) := Flat.epi_of_flat_of_surjective (spMap f)
    exact fun x y E => Over.OverMorphism.ext ((cancel_epi (spMap f)).1
      ((hr x).symm.trans ((congrArg (fun q => q.left ≫ φ) E).trans (hr y))))
  refine ⟨r, hr, inj, fun n hn y hy => ?_, fun n x y c H => ?_⟩
  · have hk : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : K') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hk
    have c₁ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hk
    have c₂ := (hL.mulN _ P' n hn).2.2.2.2 K' (𝟙 _) hk'
    let F : {x : baseOver (Sp K) ⟶ P.A // x ^ n = 1} → {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hF : Function.Injective F := fun a b E => Subtype.ext (inj (congrArg Subtype.val E))
    haveI : Finite {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (c₂.trans_ne (by positivity))
    obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (c₂.trans (by rw [h.1]; exact c₁.symm)).le).2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · have hu : Units.map U.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map f.toMonoidHom c) :=
      Units.ext (congrArg (fun q => q.hom (c : K)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
    refine (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ P.isLB P'.isLB h.2.1 h.2.2.symm _ _ _ _ (U ≫ x) (U ≫ y) _
      (hr x).symm (hr y).symm).2 ?_
    exact hu ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB U H

theorem fnOf_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (c : K) :
    fnOf (f c) = (spMap f).appTop.hom (fnOf c) :=
  congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

theorem exists_fullExt (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K) :
    letI := H.starRing
    ∃ o' : Full D K', (o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
      ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
        (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
        ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left) ∧
      (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧
      ∀ m j z v, o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  letI := H.starRing
  obtain ⟨P', φ, hφ, hg, hm, hw⟩ := hL.polBaseChange _ _ (spMap f) o.P
  have hp : IsGrpPullback P'.A o.P.A (spMap f) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have h : IsPolFibre f o.P P' φ := ⟨hg, hp, hw⟩
  obtain ⟨oa, hoa⟩ := polOActPull _ _ _ o.P P' φ hp hw (𝓞 E) o.oa
  obtain ⟨r, hr, inj, onto, weil⟩ := exists_pointMap hL h
  have uinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hact : ∀ c x, r (x ≫ o.oa.act c) = r x ≫ oa.act c := fun c x => Over.OverMorphism.ext (hφ.hom_ext (by
    rw [hr, Over.comp_left, Over.comp_left, Category.assoc, hoa, ← Category.assoc, ← Category.assoc, hr])
    (by rw [Over.w, Over.w]))
  have tors : ∀ m a, r (o.I.ev (m ^ 2) a) ^ (m ^ 2) = 1 := fun m a => by
    rcases Nat.eq_zero_or_pos (m ^ 2) with e | e
    · rw [e, pow_zero]
    · rw [← map_pow, (o.I.onto _ e _).2 ⟨a, rfl⟩, map_one]
  have det : DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K')) (f o.ρ) := fun τ => by
    have q := (detCond_iff_of_field_extension E H D _ _ K K' f (𝟙 _) _ _ o.P.isAb.smooth).2 o.det τ
    have e := fun n => LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ φ (ofRingAct o.oa.toRingAct) (ofRingAct oa.toRingAct) hp hoa
      K' (𝟙 _) τ n
    rw [e, e, Category.id_comp]
    rwa [Category.comp_id] at q
  refine ⟨{ P := P', oa := oa, prim := prim_pull hp o.P.isLB P'.isLB hw (hoa _) o.prim, ρ := f o.ρ
            ρ_sq := by rw [← map_pow, o.ρ_sq, map_neg, map_natCast]
            det := det
            closed := ‹_›
            I := { ζ := fun n => Units.map f.toMonoidHom (o.I.ζ n)
                   ζ_prim := fun n hn => (o.I.ζ_prim n hn).map_of_injective uinj
                   ζ_pow := fun n m hn hm => by rw [← map_pow, o.I.ζ_pow n m hn hm]
                   ev := fun n v => r (o.I.ev n v)
                   add := fun n a b => by rw [o.I.add, map_mul]
                   lin := fun n c a => by rw [o.I.lin, hact]
                   ker := fun n hn a => by rw [← o.I.ker n hn a, map_eq_one_iff r inj]
                   onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
                   tower := fun n m hn hm a => by rw [← map_pow, o.I.tower n m hn hm]
                   isom := fun n hn a b => by rw [← map_zpow]; exact weil _ _ _ _ (o.I.isom n hn a b) } },
    ⟨rfl, fun _ _ => rfl, φ, hp, h.2.2.symm, hoa, fun n v _ => hr _⟩, fun m v Q => ?_, fun m j z v Q => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := onto n hn z hz
    obtain ⟨a, rfl⟩ := (o.I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  · have q := ConstThetaLevel.isThetaPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) Q
    simp only [← fnOf_map] at q
    exact q
  · have q := isCoordPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) (hr (o.I.ev j z)).symm Q
    simp only [← fnOf_map] at q
    exact q

end GlobalTheory.FullExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperIffOfSplit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.AbelianLocus

theorem isProper_of_eq {S G G₁ G₂ : Scheme.{0}} (f : G ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    {K₁ K₂ : Type} [Field K₁] [Field K₂] {t₁ : Sp K₁ ⟶ S} {t₂ : Sp K₂ ⟶ S}
    {φ₁ : G₁ ⟶ G} {f₁ : G₁ ⟶ Sp K₁} {φ₂ : G₂ ⟶ G} {f₂ : G₂ ⟶ Sp K₂}
    (h₁ : IsPullback φ₁ f₁ f t₁) (h₂ : IsPullback φ₂ f₂ f t₂) (p₁ : Sp K₁) (p₂ : Sp K₂) (hp : t₁ p₁ = t₂ p₂)
    [IsProper f₁] : IsProper f₂ := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t₁) (g := t₂) p₁ p₂ hp
  let j := (pullback t₁ t₂).fromSpecResidueField z
  let u := j ≫ pullback.fst t₁ t₂
  let u' := j ≫ pullback.snd t₁ t₂
  have e : u ≫ t₁ = u' ≫ t₂ := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback f₁ u).paste_horiz h₁
  have P₂ := (IsPullback.of_hasPullback f₂ u').paste_horiz h₂
  rw [← e] at P₂
  have h₃ : UniversallyClosed (pullback.snd f₂ u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd f₂ u'), P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K₂) := inferInstanceAs (Subsingleton (PrimeSpectrum K₂))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed f₂ :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₃
  have : IsSeparated f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  have : LocallyOfFiniteType f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  exact ⟨⟩

theorem mem_abLocus_iff {S G₁ : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] {t : Sp K ⟶ S} {φ : G₁ ⟶ G.left} {f : G₁ ⟶ Sp K} (h : IsPullback φ f G.hom t)
    (p : Sp K) : t p ∈ abLocus G ↔ IsProper f := by
  constructor
  · intro hp
    let K' := AlgebraicClosure K
    let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have q : Sp K' := (default : PrimeSpectrum K')
    have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
    have := hp K' (u ≫ t) ⟨q, e⟩
    exact isProper_of_eq G.hom (IsPullback.of_hasPullback G.hom (u ≫ t)) h q p e
  · rintro hf K' _ _ t' ⟨q, hq⟩
    exact isProper_of_eq G.hom h (IsPullback.of_hasPullback G.hom t') p q hq.symm

theorem isProper_iff_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (hs : C.Split c) :
    IsProper H.hom ↔ d = 0 := by
  obtain ⟨hc, i, hi⟩ := hs
  obtain ⟨B, _, q, hB, hq, hf, hsu, ha, hp, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hi
  have := hi.hom
  constructor
  · intro hH
    have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique _ _⟩
    have : Mono i := MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hp.flip this
    have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mono K (Fin d → ℤ) H i hi.hom
    rcases d with _ | d
    · rfl
    · exact absurd (congrFun (Subsingleton.elim (0 : Fin (d + 1) → ℤ) 1) 0) zero_ne_one
  · rintro rfl
    have : Mono q := ⟨fun {Y} x y hxy => by
      have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
        rfl
      have h2 : hp.lift _ _ h1 = 1 := by
        apply (splitTorusPointsEquiv (Sp K) (Fin 0 → ℤ) Y).injective
        refine MonoidHom.ext fun a => ?_
        rw [Subsingleton.elim a 1, map_one, map_one]
      have h3 := hp.lift_fst _ _ h1
      rw [h2, MonObj.one_comp] at h3
      exact mul_inv_eq_one.1 h3.symm⟩
    have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
    have := hB.proper
    have := hB.smooth
    have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [Over.w q]; infer_instance
    have : LocallyOfFiniteType (q.left ≫ B.hom) := inferInstance
    have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp _ B.hom
    have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
    have : LocallyOfFinitePresentation q.left := inferInstance
    have : IsOpenImmersion q.left := IsOpenImmersion.of_flat_of_mono _
    have : IsIso q.left := isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext q.left.surjective.range_eq)
    rw [← Over.w q]
    infer_instance

theorem isProper_snd {P Z : Scheme.{0}} (f : P ⟶ Z) [IsProper f] (G : P.Opens) (U : Z.Opens) (h : f ⁻¹ᵁ U ≤ G) :
    IsProper (pullback.snd (G.ι ≫ f) U.ι) := by
  have h₁ := IsPullback.of_hasPullback f U.ι
  have h₂ := IsPullback.of_hasPullback G.ι (pullback.fst f U.ι)
  have h₃ := h₂.paste_vert h₁
  have : IsIso (pullback.snd G.ι (pullback.fst f U.ι)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    refine Set.eq_univ_of_forall fun x => h ?_
    have : pullback.fst f U.ι x ∈ Set.range (pullback.fst f U.ι) := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at this
  rw [← h₃.isoPullback_inv_snd]
  infer_instance

theorem abLocus_eq : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → ∀ Zab : C.Z.Opens, (∀ w : C.P.left, IsClosed ({w} : Set C.P.left) → C.P.hom w ∈ Zab → w ∈ C.G) → (∀ z : C.Z, IsClosed ({z} : Set C.Z) → z ∉ Zab → z ∉ abLocus C.GG) → abLocus C.GG = Zab ∧ IsProper (pullback.snd C.GG.hom Zab.ι) := by
  intro C L hT hC Zab h₁ h₂
  let := L.grp
  have := L.comm
  obtain ⟨hsep, hlft, hqc, -⟩ := GlobalTheory.ZJ.core_basic C
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have := C.proper
  have := C.lft
  have hle : C.P.hom ⁻¹ᵁ Zab ≤ C.G := by
    have := (GlobalTheory.jacobson_closedPoints_tools_int C.P.left (C.P.hom ≫ C.π)).2.2.1 (C.P.hom ⁻¹ᵁ Zab)
      (C.P.hom ⁻¹ᵁ Zab ⊓ C.G) fun w hw => ⟨fun h => ⟨h, h₁ w hw h⟩, fun h => h.1⟩
    exact inf_eq_left.1 this.symm
  have hpr : IsProper (pullback.snd C.GG.hom Zab.ι) := isProper_snd C.P.hom C.G Zab hle
  refine ⟨Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_), hpr⟩
  · by_contra hzn
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hs, hcl⟩ := GlobalTheory.T.exists_dense_closedPoints_chartSplitting C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have key : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R)
        [IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom s)],
        Charts.Split (H := (Over.pullback s).obj ((Over.pullback t).obj C.GG))
          (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c → ∀ p, (t (s p) ∈ abLocus C.GG ↔ d = 0) := by
      intro K _ s _ hsp p
      have : Smooth ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IsSeparated ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (IsSeparated (pullback.snd _ _))
      have : QuasiCompact ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (QuasiCompact (pullback.snd _ _))
      rw [← isProper_iff_of_split K ((Over.pullback s).obj ((Over.pullback t).obj C.GG))
        (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c hsp]
      exact mem_abLocus_iff C.GG ((IsPullback.of_hasPullback (pullback.snd C.GG.hom t) s).paste_horiz
        (IsPullback.of_hasPullback C.GG.hom t)) p
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    have hgen := GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hs
    have p₀ : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
    have hp₀ : Out.jK R p₀ = (⊥ : PrimeSpectrum R) := by
      have : p₀ = (⊥ : PrimeSpectrum (FractionRing R)) := Subsingleton.elim (α := PrimeSpectrum _) _ _
      subst this
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
    have hd0 : d = 0 := (key _ _ hgen p₀).1 (by rw [hp₀, ht]; exact hz)
    have : Nonempty (Sp R) := ⟨(⊥ : PrimeSpectrum R)⟩
    obtain ⟨x, hx⟩ := hd.nonempty
    obtain ⟨K, _, s, _, hr, hsp⟩ := hs x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range s := hr ▸ rfl
    refine h₂ _ (hcl _ hx) (fun hm => hzn ?_) ((key K s hsp p).2 hd0)
    have hsz : (⊥ : PrimeSpectrum R) ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have := (hsz.map t.continuous).mem_open Zab.2 hm
    rwa [← ht]
  · rintro K _ _ t ⟨p, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have hr : Set.range t ⊆ Set.range Zab.ι := by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim q p]
      exact hz
    have P := (IsPullback.of_hasPullback (pullback.snd C.GG.hom Zab.ι) (IsOpenImmersion.lift Zab.ι t hr)).paste_horiz
      (IsPullback.of_hasPullback C.GG.hom Zab.ι)
    rw [IsOpenImmersion.lift_fac] at P
    rw [← P.isoPullback_inv_snd]
    infer_instance

end GlobalTheory.ZJ.AbelianLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitAllAndIsSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.FibreSplit

theorem exists_residue_factor {K : Type} [Field K] {Z : Scheme.{0}} (s : Sp K ⟶ Z) [SurjectiveOnStalks s]
    (z : Z) (hz : s (IsLocalRing.closedPoint K) = z) :
    ∃ f : Sp (Z.residueField z) ⟶ Sp K, f ≫ s = Z.fromSpecResidueField z := by
  subst hz
  let ρ := Z.descResidueField (Scheme.stalkClosedPointTo s)
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp (s.stalkMap_surjective _)
  have hρ : Function.Surjective ρ.hom := by
    have h := congrArg CommRingCat.Hom.hom (Z.residue_descResidueField (Scheme.stalkClosedPointTo s))
    rw [← h] at hs
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2 ⟨ρ.hom.injective, hρ⟩
  refine ⟨inv (Spec.map ρ), ?_⟩
  rw [IsIso.inv_comp_eq]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z s).symm

theorem exists_splitExt_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (h : C.Split c) :
    ∃ E : SplitExt (Sp K), E.IsGt H := by
  obtain ⟨hc, i, hT⟩ := h
  obtain ⟨B, gB, q, hB, hq, hf, hs, ha, hk, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension K H ⟨{
    X := Fin d → ℤ, B := B, grpB := gB, isAbelian := hB, i := i, q := q, i_hom := hT.hom, q_hom := hq,
    q_flat := hf, q_surjective := hs, q_quasiCompact := inferInstance, isKernel := hk }⟩

theorem splitAll_and_isSemiAbelian : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG := by
  intro C L hT hC
  let := L.grp
  let := L.comm
  obtain ⟨hsep, -, hqc, -⟩ := core_basic C
  have := L.smooth
  have hsm : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : SplitAll C.GG := by
    intro z
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hS, -⟩ := DenseSplit.exists_dense_splitOn C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd C.GG.hom t))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd C.GG.hom t))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd C.GG.hom t))
    have : Smooth ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (Smooth (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsSeparated ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : QuasiCompact ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    obtain ⟨E, hE⟩ := exists_splitExt_of_split (FractionRing R) _ _ d _
      (GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hS)
    have : IsPreimmersion (Out.jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    obtain ⟨f, hf⟩ := exists_residue_factor (Out.jK R ≫ t) z (by
      rw [← ht]
      refine (Scheme.Hom.comp_apply (Out.jK R) t _).trans (congrArg t (PrimeSpectrum.ext ?_))
      change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)])
    have : IsMonHom (pullCompIso (Out.jK R) t C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (Out.jK R) t C.GG).inv)
    obtain ⟨D⟩ := isGt_of_iso (pullCompIso (Out.jK R) t C.GG).symm hE
    have : IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).inv)
    have key : ∀ s : Sp (C.Z.residueField z) ⟶ C.Z, f ≫ Out.jK R ≫ t = s →
        ∃ E : SplitExt (Sp (C.Z.residueField z)), E.IsGt ((Over.pullback s).obj C.GG) := by
      rintro _ rfl
      exact ⟨_, isGt_of_iso (pullCompIso f (Out.jK R ≫ t) C.GG).symm (GtBaseChange.isGt_extBC f E _ D)⟩
    exact key _ hf
  exact ⟨h, (isSemiAbelian_of_splitAll C.Z C.GG h).1⟩

end GlobalTheory.ZJ.FibreSplit
end

