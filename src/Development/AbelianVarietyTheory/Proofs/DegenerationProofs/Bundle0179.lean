module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedThetaConstantsPrimitiveIntegralOneUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

theorem GlobalTheory.Ex.OneGen.thG_val_of_prim : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  rintro ⟨hLL, h₁, h₂, h₃, h₄⟩ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hw th ϑ hex hprim m hmo hmu hm
  have hAdm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨f, hf, hfs, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hLL V _ hAdm D A G hG U F (m ^ 2) (pow_pos hmo.pos 2)
  obtain ⟨ua, ub⟩ := _root_.GlobalTheory.UT.ThetaConstVal.main hLL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hw th ϑ hex hprim m hmo hmu
  refine ⟨fun x c H => ?_, ?_⟩
  · obtain ⟨hx, t, ht⟩ := (thG_iff A ρ m th x c).1 H
    obtain ⟨p, hp⟩ := hfs x hx
    refine (ua p x t c ((hf p x).2 hp.symm) ht).1 0 fun χ => div_nonneg ?_ (Nat.cast_nonneg _)
    by_cases h : m • χ + p.y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]; simp
    · exact_mod_cast zero_le_one.trans (QForm.Q_pos hϖ D hQ h)
  · obtain ⟨p', x', t, c, -, hx', -, hc, hz⟩ := ub m (by omega) dvd_rfl (TorusExt.qkZero D.tau_bimult F _) _ rfl
      ((hf _ _).2 rfl)
    exact ⟨x', c, (thG_iff A ρ m th x' c).2 ⟨(hx' w₀ hw.1).1, t, hc⟩, hz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.RelabelCoords

theorem isCoordPt_unit_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type} {x : I → (T ⟶ P.A)}
    {z : T ⟶ P.A} {v w : I → Γ(T.left, ⊤)} (u : Γ(T.left, ⊤)ˣ) (h8 : ∀ i, v i = u.val * w i)
    (H : IsCoordPt P k x z w) : IsCoordPt P k x z v := by
  obtain ⟨ho, hu, th, s1, α, τ, U, s2, h1, h2, h3, h4, h5, h6, h7⟩ := H
  refine ⟨ho, hu, th, s1, α, ⟨fun j => τ.s j * InhTate.gv u⁻¹ _⟩, U, s2, h1, h2, fun i j => ?_, h4, h5, h6, fun i j => ?_⟩
  · rw [map_mul, map_mul, h3 i j, InhTate.res_gv, InhTate.res_gv, _root_.mul_assoc]
  · rw [h7 i j, h8 i, map_mul]
    have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom u.val *
        (T.left.presheaf.map (homOfLE (le_top : LB.wchart P.L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom
          (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have key : ∀ {A : Type} [CommRing A] (a b c d : A), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
      linear_combination (-(c * d)) * h
    exact key _ _ _ _ e

theorem twRel_unique {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ} {q : N.QT j}
    {p p' : (N.twist β u).QT j} (h : TwRel β u r q p) (h' : TwRel β u r q p') : p = p' :=
  Subtype.ext (Prod.ext (h.1.trans h'.1.symm)
    (NumD.Gt.ext (h.2.1.trans h'.2.1.symm) (funext fun z => (h.2.2 z).trans (h'.2.2 z).symm)))

theorem series_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2) :
    N.tx m p = (J.lam⁻¹ : Cˣ) * N'.tx m p' ∧
      ∀ g g', J.Rel g g' → N.ev m p g = ((J.lam * J.h g.b ^ (m ^ 2))⁻¹ : Cˣ) * N'.ev m p' g' := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  refine ⟨?_, fun g g' hg => ?_⟩
  · have e : N'.tx m p' = J.lam * N.tx m p := by
      rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).1
    rw [e, Units.inv_mul_cancel_left]
  · have e : N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
      rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun χ => (H χ).2 g g' hg
    rw [e, Units.inv_mul_cancel_left]

theorem theta_coord : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  intro hL hB hT hE E _ _ _ H D C _ _ _ _ _ o M I N N' ν' k β u r J q hq m hm p hp
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  choose q' p' x htw hqp hx hA using hq (m ^ 2) hm2
  have hJ : ∀ a, (q' a).1.1.toAdd = J.e (p a).1.1.toAdd ∧ J.Rel (p a).1.2 (q' a).1.2 := fun a => by
    obtain ⟨p₁, h₁, h₂⟩ := htw a
    rwa [twRel_unique h₁ (hp a)] at h₂
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have hx' : ∀ a, τ ≫ (x a).left = (I.ev (m ^ 2) a).left ≫ M.φ := fun a => (Category.id_comp _).trans (hx a)
  have hk : ∀ a, I.ev (m ^ 2) a ^ (m ^ 2) = 1 := fun a => (I.onto _ hm2 _).2 ⟨a, rfl⟩
  have hs : Subsingleton (Sp C) := inferInstanceAs (Subsingleton (PrimeSpectrum C))
  have hn : Nonempty (Sp C) := inferInstanceAs (Nonempty (PrimeSpectrum C))
  have hτv : ∀ (c : Cˣ) (a : C), fnOf (c * a) = (unitOn c).val * (show Γ(Sp C, ⊤) from τ.appTop.hom (fnOf a)) := fun c a =>
    map_mul (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom _ _
  refine ⟨?_, fun j hj z p₀ h₀ => ?_⟩
  · have Q := hT M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
    have : Subsingleton (TFK (R := M.W) C).left := hs
    have : Nonempty (TFK (R := M.W) C).left := hn
    have : Subsingleton (baseOver (Sp C)).left := hs
    have Q₁ := ThetaPtUp.isThetaPtOver_down τ M.cart M.lb hτ hx' hk (ThetaCoord.isThetaPtOver_of_subsingleton _ Q)
    have Q₂ := (isCoordPt_one_iff o.P m (T := baseOver (Sp C)) _ _).2 ⟨hm, Q.2.1, Q₁⟩
    have Q₃ := isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).tx m (p a))) (unitOn J.lam⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).1]; exact hτv _ _) Q₂
    exact ThetaNest.isThetaPt_of_over _ hm Q.2.1 ((isCoordPt_one_iff _ _ _ _).1 Q₃).2.2
  · obtain ⟨q₁, p₁, y, ⟨p₂, t₁, -, t₂⟩, hq₁, hy, hA₁⟩ := hq j hj z
    obtain rfl := twRel_unique h₀ t₁
    let q₄ : N'.QT (j * 4) := ⟨(q₁.1.1 ^ 4, q₁.1.2), by
      rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 q₁.2, toAdd_pow, NumD.io_nsmul]⟩
    have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
    obtain ⟨p₄, hp₄⟩ := (B.2.2.2.2 (j * 4)).2.1 q₄
    have e₁ : p₄.y = 4 • p₁.y := by
      rw [← hp₄.1, ← hq₁.1, ← map_nsmul]; rfl
    have e₂ : p₄.g = p₁.g := (B.2.1 q₁.1.2).unique hp₄.2 hq₁.2
    have := M.admissible_base_of_complete_dvr.2
    have hA₄ := ((_root_.GlobalTheory.LevelCompat.qkToAkU_level hL M.W _ M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi M.P.U C j 4 (j * 4) hj (by norm_num) rfl
      p₁ p₄ y).1 e₁ e₂).1 hA₁
    have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm D.La p' q' x hA hqp
      (j * 4) (by omega) p₄ q₄ y hA₄ hp₄
    have Q₁ := FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      hx' hk (z := I.ev j z) ((Category.id_comp _).trans hy) Q
    exact isCoordPt_unit_mul (v := fun a => fnOf ((N.twist β u).ev m (p a) p₀.1.2))
      (unitOn (J.lam * J.h p₀.1.2.b ^ (m ^ 2))⁻¹)
      (fun a => by rw [(series_iso J hm (hJ a).1 (hJ a).2).2 _ _ t₂]; exact hτv _ _) Q₁

end GlobalTheory.RelabelCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionTorsionMemUnitThetaConstantGroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGen
open GlobalTheory.TorusExt

theorem mem_of_step {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M) (n j : ℕ) (h₀ : ∀ t, φ t ^ (n ^ j) = 1)
    (h : ∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) (t : T) : φ t ∈ S := by
  have key : ∀ i : ℕ, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ (n ^ i) := fun i => by
    induction i with
    | zero => exact ⟨1, S.one_mem, t, by simp⟩
    | succ i ih =>
      obtain ⟨s, hs, t', e⟩ := ih
      obtain ⟨s', hs', t'', e'⟩ := h t'
      refine ⟨s * s' ^ (n ^ i), S.mul_mem hs (S.pow_mem hs' _), t'', ?_⟩
      rw [e, e', mul_pow, ← pow_mul, _root_.mul_assoc, pow_succ']
  obtain ⟨s, hs, t', e⟩ := key j
  rwa [e, h₀, _root_.mul_one]

attribute [local instance] gtGroup

theorem exists_hom {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [CommGroup M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') :
    ∃ φ : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker →+ Additive M,
      ∀ t (p : QkPt D F k), p.y = 0 → p.g = t.1 → φ t = Additive.ofMul (f p) := by
  have hiota0 : ∀ (h : GtPtF D F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D (T := TF (R := R) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let qkMk (g : GtPtF D F) (h : k • g = 0) : QkPt D F k :=
    ⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, hiota0 _ ((isZero_iff_eq _).2 h)⟩
  let r : (nsmulAddMonoidHom k : GtPtF D F →+ GtPtF D F).ker → QkPt D F k := fun t =>
    qkMk t.1 t.2
  refine ⟨AddMonoidHom.mk' (fun t => Additive.ofMul (f (r t))) fun t t' => ?_, fun t p hy hg => ?_⟩
  · let p := qkMk (t.1 + t'.1) (by rw [nsmul_add, show k • t.1 = 0 from t.2, show k • t'.1 = 0 from t'.2, add_zero])
    have hp : QkAdd (r t) (r t') p :=
      ⟨p, by simp [p, qkMk, r], (isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB p⟩
    rw [← ofMul_mul, ← hf _ _ _ hp]
    exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext rfl rfl)
  · exact congrArg (fun p => Additive.ofMul (f p)) (qk_ext (by simpa [r] using hy.symm) hg.symm)

theorem fromGt_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN theta ϑ hE hP n j hn ho hu hj x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hdvd₂ : n * n ∣ n ^ j := by rw [← pow_two]; exact pow_dvd_pow n hj
  have hm : Odd (n ^ j) := ho.pow
  have hum : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hu.pow j
  have kill : ∀ {M : Type} [CommGroup M]
      (φ : (nsmulAddMonoidHom (n ^ j) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker →+ Additive M) t,
      Additive.toMul (φ t) ^ (n ^ j) = 1 := fun φ t => by
    rw [← toMul_nsmul, ← map_nsmul, show (n ^ j) • t = 0 from Subtype.ext t.2, map_zero, toMul_zero]
  have ua := (_root_.GlobalTheory.UT.ThetaConstVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN theta ϑ hE hP _ hm hum).2 n hn.two_le hdvd
  have fin : ∀ {M T : Type} [CommGroup M] (S : Subgroup M) (φ : T → M), (∀ t, φ t ^ (n ^ j) = 1) →
    (∀ t, ∃ s ∈ S, ∃ t', φ t = s * φ t' ^ n) → ∀ t, φ t ∈ S := fun S φ => mem_of_step S φ n j
  generalize n ^ j = m at *
  have m1 : 1 ≤ m := hm.pos
  have div := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have lev := fun p q x => (_root_.GlobalTheory.LevelCompat.qkToAkU_level hL V _ hA D A G hG U F m m (m ^ 2) m1 m1 (pow_two m) p q x).2
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F m m1
  obtain ⟨f', f₁', -, -, f₄', -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨φ, hφ⟩ := exists_hom hB f f₄
  obtain ⟨φ', hφ'⟩ := exists_hom hB f' f₄'
  have hiota0 : ∀ (h : GtPtF D.toPre F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D.toPre (T := TF (R := V) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  have mem : ∀ {k} (p : QkPt D.toPre F k), p.y = 0 →
      p.g ∈ (nsmulAddMonoidHom k : GtPtF D.toPre F →+ GtPtF D.toPre F).ker := fun {k} p hy => by
    show k • p.g = 0
    obtain ⟨g, h₁, h₂⟩ := p.eq
    rw [hy] at h₂
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans (isIota_unique h₂ (hiota0 _ ((isZero_iff_eq _).2 rfl)))
  have mk : ∀ {k : ℕ} (g : GtPtF D.toPre F), k • g = 0 → ∃ p : QkPt D.toPre F k, p.y = 0 ∧ p.g = g := fun {k} g h =>
    ⟨⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl,
      hiota0 _ ((isZero_iff_eq _).2 h)⟩, rfl, rfl⟩
  have inj : ∀ t, φ t = 0 → t = 0 := fun t ht => by
    obtain ⟨p, py, pg⟩ := mk t.1 t.2
    obtain ⟨o, oy, og⟩ := mk (k := m) 0 (nsmul_zero m)
    have e : f o = f p := Additive.ofMul.injective (by rw [← hφ t p py pg, ← hφ 0 o oy og, ht, map_zero])
    obtain ⟨z, hy, g, hg₁, hg₂⟩ := (f₃ _ _).1 e
    rw [py, oy, zero_add] at hy
    have z0 : z = 0 := by
      by_contra h0
      have b₁ := QForm.Q_pos hϖ D hQ h0
      have b₂ := Q_nsmul hϖ hQ m z
      rw [← hy, QForm.Q_zero hϖ D hQ] at b₂
      have b₃ : (0 : ℤ) < (m : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
      exact absurd b₂ (mul_pos b₃ (by omega)).ne
    rw [z0] at hg₁
    have hg0 : g = 0 := isIota_unique hg₁ (hiota0 _ ((isZero_iff_eq _).2 rfl))
    have hg := (isAdd_iff_eq _ _ _).1 hg₂
    rw [hg0, add_zero, pg, og] at hg
    exact Subtype.ext hg
  obtain ⟨p, py, hp⟩ := hx
  have ex : x = Additive.toMul (φ ⟨p.g, mem p py⟩) := by rw [hφ _ p py rfl, (f₁ p x).1 hp]; rfl
  rw [ex]
  refine fin _ (fun t => Additive.toMul (φ t)) (kill φ) (fun t => ?_) _
  obtain ⟨r, ry, rg⟩ := mk t.1 t.2
  obtain ⟨g', hg'⟩ := div m m1 t.1
  have e₁ : t.1 = m • g' := (isNsmul_iff_eq _ _ _).1 hg'
  obtain ⟨q, qy, qg⟩ := mk (k := m ^ 2) g' (by rw [pow_two, mul_smul, ← e₁]; exact t.2)
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f' q) := (f₁' _ _).2 rfl
  have e₂ : f' q ^ m = Additive.toMul (φ t) := by
    rw [hφ t r ry rg]
    exact (f₁ _ _).1 (lev r q _ (ry.trans qy.symm) (by rw [qg, rg]; exact hg') hq)
  obtain ⟨p', x', t₁, c, py', hx', hn', hT, hc₀⟩ := ua q _ qy hq
  have x1 : x' ^ (m ^ 2) = 1 := by
    rw [(f₁' _ _).1 hx']
    have := congrArg Additive.toMul (hφ' ⟨_, mem p' py'⟩ p' py' rfl)
    rw [toMul_ofMul] at this
    rw [← this, ← toMul_nsmul, ← map_nsmul,
      show (m ^ 2) • (⟨_, mem p' py'⟩ : (nsmulAddMonoidHom (m ^ 2) : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = 0 from
        Subtype.ext (mem p' py'), map_zero, toMul_zero]
  obtain ⟨s, sy, sg⟩ := mk (k := m) (m • p'.g) (by rw [← mul_smul, ← pow_two]; exact mem p' py')
  have e₃ : x' ^ m = Additive.toMul (φ ⟨_, mem s sy⟩) := by
    rw [hφ _ s sy rfl]
    exact (f₁ _ _).1 (lev s p' _ (sy.trans py'.symm) ((isNsmul_iff_eq _ _ _).2 sg) hx')
  refine ⟨x' ^ m, Subgroup.subset_closure ⟨x', t₁, c, x1, hT, hc₀, rfl⟩, ?_⟩
  rw [e₂, e₃] at hn'
  rw [e₃]
  generalize (⟨_, mem s sy⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = a at hn'
  have z : n • (a - t) = 0 := inj _ (by
    rw [map_nsmul, map_sub]
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_sub, div_eq_mul_inv, hn', toMul_zero])
  obtain ⟨w, hw⟩ := div n hn.one_le (t - a).1
  have e₄ : (t - a).1 = n • w := (isNsmul_iff_eq _ _ _).1 hw
  have z' : n • (t - a) = 0 := by rw [← neg_sub, smul_neg, z, neg_zero]
  have wm : m • w = 0 := by
    obtain ⟨d, hd⟩ := hdvd₂
    have : n • (t - a).1 = 0 := congrArg Subtype.val z'
    rw [hd, _root_.mul_comm, mul_smul, mul_smul, ← e₄, this, smul_zero]
  refine ⟨⟨w, wm⟩, ?_⟩
  show Additive.toMul (φ t) = Additive.toMul (φ a) * Additive.toMul (φ ⟨w, wm⟩) ^ n
  rw [← toMul_nsmul, ← map_nsmul, ← toMul_add, ← map_add (f := _),
    show n • (⟨w, wm⟩ : (nsmulAddMonoidHom m : GtPtF D.toPre F →+ GtPtF D.toPre F).ker) = t - a from
      Subtype.ext e₄.symm, add_sub_cancel]

end GlobalTheory.OneBasis.UnitGen
end
end

