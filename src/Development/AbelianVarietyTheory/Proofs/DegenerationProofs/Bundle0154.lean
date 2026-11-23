module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.LiftExt
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Field F']
    [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] [Algebra (FractionRing R) F'']
    {f : F →+* F'} {f' : F' →+* F''} {k : ℕ} {p : QkPt D F k} {p' : QkPt D F' k} {p'' : QkPt D F'' k}
    (h : QkExt f p p') (h' : QkExt f' p' p'') : QkExt (f'.comp f) p p'' := by
  have e : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp' f f'
  refine ⟨h'.1.trans h.1, by rw [h'.2.1, h.2.1, e, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

theorem equiv_of_base {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p₀ : QkPt D (FractionRing R) k} {r : QkPt D F k}
    (h : ∀ p, QkExt (algebraMap (FractionRing R) F) p₀ p → QkPt.Equiv D F p r) (p' : QkPt D F' k)
    (hp' : QkExt (algebraMap (FractionRing R) F') p₀ p') : QkPt.Equiv D F' p' (qkExt hB f hf r) := by
  obtain ⟨p, hp, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing R) F) (RingHom.ext fun _ => rfl) p₀
  have h₁ := qkExt_trans hp ((qkExt_iff hB f hf p _).2 rfl)
  rw [hf] at h₁
  rw [(existsUnique_qkExt hB (algebraMap (FractionRing R) F') (RingHom.ext fun _ => rfl) p₀).unique hp' h₁]
  exact qkExt_congr hB f hf (h p hp)

theorem exists_lift_ext : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  intro hL hGt hWp E _ _ _ H D l Xo c W₀ Y R _ _ _ b ϖ a _ F F' _ _ _ _ _ _ f hf S hS A
  have hf₀ : ∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x := fun x =>
    DFunLike.congr_fun hf x
  have : CharZero F := charZero_of_isPrimitiveRoot A.I.ζ_prim
  obtain ⟨J', hg, hJ⟩ := GlobalTheory.ValuesExist.exists_gauge F' S a.D₀.P.isLB
  obtain ⟨N', ν', rfl, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R a.D₀ a.even a.bimult F' J' hg A.ν.th A.ν.th_gen
  have G := (hGt R a.D₀ a.even a.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R a.D₀ a.even a.bimult F' N' ν').2.2.2.2
  obtain ⟨I, hlam, heX, hI⟩ := GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension R a.D₀ F F' f hf A.N N' A.ν ν' hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt a.D₀ F k) (z : F), WeilQkIs a.D₀ F k p p' z →
      WeilQkIs a.D₀ F' k (qkExt a.bimult f hf p) (qkExt a.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt a.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt a.bimult f hf p')
    have e := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq hr
    have e' := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq' hr'
    rw [hWp R a.D₀ a.even a.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (_root_.GlobalTheory.Ex.NumD.hom_transport F F' f A.N N' I).2.2.2.1 k q q' r r' e.1 e.2 e'.1 e'.2,
      (hWp R a.D₀ a.even a.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (v : D.La) => ((G' n).1 (qkExt a.bimult f hf (A.I.ev n v))).exists
  refine ⟨{ ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf a.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq'
            be := { be := a.be.compl₁₂ ν'.eX.toAddMonoidHom.toIntLinearMap ν'.eX.toAddMonoidHom.toIntLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ fun h => hy (ν'.eX.map_eq_zero_iff.1 h)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r hr => (congrArg f (A.ρ_eq r hr)).trans (hf₀ _)
            ζ_eq := fun z hz => (congrArg f (A.ζ_eq z hz)).trans (hf₀ _)
            levA := fun v => equiv_of_base a.bimult f hf (A.levA v)
            levM := fun v hv => equiv_of_base a.bimult f hf (A.levM v hv)
            closed := inferInstance },
    fun x => hJ _ (GlobalTheory.ValuesExist.exists_ext a.D₀ F' S hS x), I, hlam, rfl, fun _ _ => rfl, heX,
    fun n v => hI n _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) (A.hq n v) (hq' n v)⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
  obtain ⟨n, h₁, h₂⟩ := A.det τ
  have := a.D₀.P.isAb.smooth
  refine ⟨n, ?_, h₂.trans (by
    by_cases h : τ H.rt = A.ρ
    · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
    · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
  have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
      spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    rw [← spMap_comp', ← RingHom.comp_assoc, hf]
  rw [e]
  exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁

end GlobalTheory.LiftExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.TorsionField

open GlobalTheory.Ex.UnifModel

theorem exists_descend_algClosed (hM : MulNSt) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Field C]
    [IsAlgClosed C] [CharZero C] (P : PolAV (Sp K)) (a : K →+* F) (i : F →+* C) (c : K →+* C)
    (h : ∀ x, i (a x) = c x) {n : ℕ} (hn : 1 ≤ n) (x : Over.mk (spMap c) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (spMap a) ⟶ P.A, y ^ n = 1 ∧ spMap i ≫ y.left = x.left := by
  have hC : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hF : (n : F) ≠ 0 := fun e => hC (by rw [← map_natCast i, e, map_zero])
  have c₁ := (hM _ P n hn).2.2.2.2 C (spMap c) hC
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap a) hF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  let u : Over.mk (spMap c) ⟶ Over.mk (spMap a) := Over.homMk (spMap i) (spMap_comp h)
  let Φ : {y : Over.mk (spMap a) ⟶ P.A // y ^ n = 1} → {y : Over.mk (spMap c) ⟶ P.A // y ^ n = 1} :=
    fun y => ⟨u ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩
  have := epi_spMap i
  have hΦ : Function.Injective Φ := fun y y' e =>
    Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap i)).1 congr(($e).1.left)))
  obtain ⟨y, hy⟩ := (hΦ.bijective_of_nat_card_le (c₁.trans c₂.symm).le).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congr(($hy).1.left)⟩

theorem exists_finset (hM : MulNSt) {K F : Type} [Field K] [Field F] [IsAlgClosed F] [CharZero F] [Algebra K F]
    [Algebra.IsAlgebraic K F] (P : PolAV (Sp K)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
      (∀ c ∈ s, c ∈ β.fieldRange) → ∀ x : Over.mk (spMap (algebraMap K F)) ⟶ P.A, x ^ n = 1 →
        ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.left := by
  classical
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap (algebraMap K F)) (Nat.cast_ne_zero.2 (by omega))
  have := Nat.finite_of_card_ne_zero (c₂ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  have := Fintype.ofFinite {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}
  have hpr := P.isAb.proper
  have key : ∀ x : {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}, ∃ s : Finset F,
      ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
        (∀ c ∈ s, c ∈ β.fieldRange) → ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h2, h3⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left F x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ := (Submodule.fg_top L.toSubalgebra.toSubmodule).1 hL.fg_top
    refine ⟨s, fun k _ β h₁ h₂ => (h2 k β).1 fun c hc => ?_⟩
    have hc' : c ∈ Submodule.span K (s : Set F) := hs ▸ hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem c hc => exact h₂ c hc
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul r c _ hc => rw [Algebra.smul_def]; exact mul_mem (h₁ r) hc
  choose s hs using key
  exact ⟨Finset.univ.biUnion s, fun k _ β h₁ h₂ x hx => hs ⟨x, hx⟩ k β h₁ fun c hc =>
    h₂ c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem exists_finset_ratTors (hL : Laws) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Algebra K F]
    [Algebra.IsAlgebraic K F] [Field C] [IsAlgClosed C] [CharZero C] (i : F →+* C) {S : Scheme.{0}} (t : Sp K ⟶ S)
    (B₁ : PolAV S) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) C] (β : FractionRing R →+* F),
      (∀ c, i (β c) = algebraMap _ C c) → (∀ c, algebraMap K F c ∈ β.fieldRange) → (∀ c ∈ s, c ∈ β.fieldRange) →
      ∀ r : Sp R ⟶ S, spMap β ≫ jK R ≫ r = spMap (algebraMap K F) ≫ t →
      ∀ (B : PolAV (Sp R)) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A r ψ → RatTors B C n := by
  have : CharZero F := i.charZero
  obtain ⟨P, φ, hφ₀, -, hm, -⟩ := hL.polBaseChange S (Sp K) t B₁
  have hφ : IsGrpPullback P.A B₁.A t φ := ⟨hφ₀, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ₀.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ₀.w y), ← hm]
    rfl⟩
  obtain ⟨s, hs⟩ := exists_finset (F := F) hL.mulN P hn
  refine ⟨s, fun R _ _ _ β hβ h₁ h₂ r hr B ψ hψ x hx => ?_⟩
  have e₁ : spMap i ≫ spMap β = jFK (R := R) C := spMap_comp hβ
  have e₂ : spMap i ≫ spMap (algebraMap K F) = spMap (i.comp (algebraMap K F)) := spMap_comp fun _ => rfl
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hψ (jFK (R := R) C ≫ jK R) _ rfl
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap (i.comp (algebraMap K F)))
    ((jFK (R := R) C ≫ jK R) ≫ r) (by rw [← e₁, ← e₂, Category.assoc, Category.assoc, hr, Category.assoc])
  obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hL.mulN P (algebraMap K F) i _ (fun _ => rfl) hn
    (e'.symm (e x)) (by rw [← map_pow, ← map_pow, hx, map_one, map_one])
  obtain ⟨z, hz⟩ := hs _ β h₁ h₂ y hy
  have := epi_spMap β
  have w : (z ≫ φ) ≫ B₁.A.hom = jK R ≫ r := by
    rw [← cancel_epi (spMap β), hr, Category.assoc, hφ₀.w, reassoc_of% hz]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (Over.w y))
  refine ⟨Over.homMk (hψ.1.lift _ _ w) (hψ.1.lift_snd _ _ _), hψ.1.hom_ext ?_ ?_⟩
  · refine (he x).symm.trans ?_
    rw [← e'.apply_symm_apply (e x), he', ← hy', ← hz, ← e₁]
    simp only [Category.assoc]
    exact congrArg (fun q => spMap i ≫ spMap β ≫ q) (hψ.1.lift_fst _ _ w).symm
  · refine (Over.w x).trans ?_
    exact (congrArg (fun q => jFK (R := R) C ≫ q) (hψ.1.lift_snd _ _ w).symm).trans (Category.assoc _ _ _).symm

theorem exists_cDvr_ratTors : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  intro hL W _ _ _ ⟨d, hc, h0⟩ C _ _ _ _ hext n hn S₁ S₂ s₁ s₂ B₁ B₂
  classical
  let F := algebraicClosure (FractionRing W) C
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed
  let : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra
  have : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have iW : Function.Injective (algebraMap W F) :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).2 iW
  have : Algebra.IsAlgebraic W F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance
  have : CharZero (FractionRing W) := IsFractionRing.charZero_of_isFractionRing W
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨t₁, ht₁⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₁) B₁ hn
  obtain ⟨t₂, ht₂⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₂) B₂ hn
  obtain ⟨V, dV, cV, -, fV, -, lV, hV, -⟩ := exists_complete_dvr_finite_subalgebra W F (t₁ ∪ t₂)
  have i₁ : Function.Injective (algebraMap V F) := Subtype.val_injective
  let β : FractionRing V →+* F := IsFractionRing.lift i₁
  have hβ : ∀ x, β (algebraMap V _ x) = algebraMap V F x := IsFractionRing.lift_algebraMap i₁
  let : Algebra (FractionRing V) C := ((algebraMap F C).comp β).toAlgebra
  have hA : Along (algebraMap W V) C := fun x => congrArg (algebraMap F C) (hβ _)
  have h₁ : ∀ c, algebraMap (FractionRing W) F c ∈ β.fieldRange := fun c => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) c
    rw [map_div₀]
    exact div_mem ⟨_, hβ (algebraMap W V a)⟩ ⟨_, hβ (algebraMap W V b)⟩
  have h₂ : ∀ c ∈ t₁ ∪ t₂, c ∈ β.fieldRange := fun x hx => by
    obtain ⟨u, hu, v, hv, h0, e⟩ := hV x hx
    refine ⟨algebraMap V _ ⟨u, hu⟩ / algebraMap V _ ⟨v, hv⟩, ?_⟩
    rw [map_div₀, hβ, hβ]
    exact (div_eq_iff h0).2 e.symm
  have e : spMap β ≫ jK V ≫ spMap (algebraMap W V) = spMap (algebraMap (FractionRing W) F) ≫ jK W := by
    rw [← Category.assoc, spMap_comp hβ, spMap_comp (d := algebraMap W F) fun _ => rfl]
    exact (spMap_comp fun _ => rfl).symm
  have : CharZero V := (algebraMap V F).charZero
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap W V, ⟨dV, cV, inferInstance⟩,
    fun a b h => iW (congrArg Subtype.val h), RingHom.finite_algebraMap.2 fV, lV, hA, cExt_of_integral hext hA,
    ht₁ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_left _ hc)) _ ?_,
    ht₂ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_right _ hc)) _ ?_⟩
  · rw [reassoc_of% e]
  · rw [reassoc_of% e]

end GlobalTheory.Ex.TorsionField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem exists_torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, IsIso.inv_comp_eq, hτ, ← Category.assoc, Over.w])
  have e : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, e, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem exists_torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have w : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ _).symm
  refine ⟨x, e, Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  rw [← over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem secRel_smul {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ} {B : Over S}
    (σ : T.left ⟶ B.left) (hσ : σ ≫ B.hom = T.hom ≫ f) (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ)
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w th th₀)
    {th' : LB.Sec (LPow G L₀ a B)} {c : Γ(B.left, ⊤)}
    (hc : SecM.ofSec G th' = c • SecM.ofSec G (VVRank.pullS G a β th₀)) :
    SecRel hp σ hσ w (SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) th' := by
  intro Z r z J J' hJ hJ'
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  rw [sv_of_eq_mul (s := th') (t := VVRank.pullS G a β th₀) (c := c) (fun j => congrArg (fun q => q.1 j) hc) _ z hJ,
    sv_of_eq_mul (s := SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) (t := th) (c := σ.appTop.hom c)
      (fun j => rfl) _ z hJ',
    VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc r _ (β ▷ G).left, e, h _ _ _ _ _ hJ hJ', mul_left_comm,
    Category.assoc r _ (fst B G).left, psi_fst', ← Category.assoc]
  exact congrArg (fun q => _ * (q * _)) (gs_pull _ σ z ⊤ trivial c).symm

end Pts

theorem exists_gen_thG_generic : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  intro hLaw _ S G _ L ρ hL hρ K _ _ _ x₀ P φ hp ⟨w, hw⟩ m hm Ix x v hx hv
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hx' : ∀ i, x i ^ (m ^ 2) = 1 := fun i => (hx _).2 ⟨i, rfl⟩
  obtain ⟨thP, hg, hth⟩ := _root_.GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt K P ρ' hρ' m Ix x v hx' hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x₀).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x₀).hom = (baseOver (Sp K)).hom ≫ x₀ := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := exists_secRel_up hp τ hτ hw hL hL₁ thP
  refine ⟨th, ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg, fun F _ _ e x' h a th' hth' => ?_⟩
  choose y hy hy' using fun i => exists_torsion_up hp τ hτ (x i) (hx' i)
  have up : ∀ i, ThG G L ρ m th (y i) (fnOf (v i)) := fun i => by
    have q := ThG.up hp τ hτ hw hL hL₁ hr (hy i) (hy' i) hrel (hth i)
    rw [hi] at q
    exact q
  let T' : Over (Sp K) := Over.mk (spMap e)
  let u : T' ⟶ baseOver (Sp K) := Over.homMk (spMap e) (Category.comp_id _)
  let τ' : T'.left ⟶ (Over.mk x₀).left := spMap e
  have hτ' : τ' ≫ (Over.mk x₀).hom = T'.hom ≫ x₀ := rfl
  let σ : T'.left ⟶ (Over.mk x').left := 𝟙 (Sp F)
  haveI : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp F)))
  have hσ : σ ≫ (Over.mk x').hom = T'.hom ≫ x₀ := (Category.id_comp _).trans h.symm
  have hj : inv σ = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨t, ht⟩ := exists_secRel hp τ' hτ' hw hL hL₁ th
  have hrel' := secRel_smul hp τ' hτ' σ hσ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀)
    (Category.id_comp _) ht hth'
  have hu : ∀ i, (u ≫ x i) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, hx', MonObj.comp_one]
  have down : ∀ i, ThG P.A P.L ρ' m (SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) (u ≫ x i)
      (fnOf (a * e (v i))) := fun i => by
    have e₁ : τ' ≫ (y i).left = (u ≫ x i).left ≫ φ :=
      (congrArg (spMap e ≫ ·) ((Category.id_comp _).symm.trans (hy i))).trans (Category.assoc _ _ _).symm
    have q := ThG.smul (th' := SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) hL₁ rfl
      (ThG.move hp τ' hτ' hw hL hL₁ hr e₁ (hu i) ht (up i))
    have e₂ : σ.appTop.hom (fnOf a) * τ'.appTop.hom (fnOf (v i)) = fnOf (a * e (v i)) :=
      (congrArg (fnOf a * ·)
        (congrArg (fun q => q.hom (v i)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm).trans
        (map_mul (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom _ _).symm
    rw [e₂] at q
    exact q
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hm.pos.ne')
  refine ⟨fun i => ?_, fun z c hz => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := exists_torsion_up hp σ hσ _ (hu i)
    have q := ThG.up hp σ hσ hw hL hL₁ hr hz hz' hrel' (down i)
    rw [hj] at q
    exact ⟨z, q⟩
  · obtain ⟨z', hz₁, hz₂⟩ := exists_torsion_down hp σ hσ z hz.1
    obtain ⟨y', hy₁, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed hLaw P u hK
      (by rw [← map_natCast e]; exact (map_ne_zero e).2 hK) z' hz₂
    obtain ⟨i, rfl⟩ := (hx y').1 hy₁
    have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
      exact (IsUnit.mk0 _ hK).map _
    have q : fnOf c = fnOf (a * e (v i)) :=
      ThG.unique hLaw P hm hun (ThG.move hp σ hσ hw hL hL₁ hr hz₁ hz₂ hrel' hz) (down i)
    exact ⟨i, (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective q⟩

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGroupLawSmoothProperModelOfGeneric
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

open SpreadAb (grpObj_of_dominant isPullback_square)

theorem exists_grpObj : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  intro R K _ _ _ _ _ _ X f A _ _ φ h _ _
  obtain ⟨a₁, ha₁, H₁⟩ := exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨a₂, ha₂, H₂⟩ := exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨a₃, ha₃, H₃⟩ := exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  refine ⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃,
    fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hg
  obtain ⟨⟨u₁, u₂⟩, u₃⟩ := hg
  have hc : spMap ψ ≫ spMap g = spMap (algebraMap R K) := by
    rw [← hψg, ← Spec.map_comp]; rfl
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ
  have : Flat G.hom := MorphismProperty.of_isPullback (P := @Flat) hG inferInstance
  have : IsSeparated G.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' g u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' g u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hc
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem exists_pelUnif_baseChange : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  intro h1 h3 h4 h5 E _ _ _ H R R' _ _ _ _ I I' hR hR' g hg hI t P
  obtain ⟨t', m₀, P', hD, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5
    hR hR' t P g hg hI
  have := hD.e_hom
  exact ⟨t', m₀, P', hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g),
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback P.D.toPre.P.A (specOf g))).congr
      (Category.id_comp _) rfl⟩

end GlobalTheory.Ex.Trait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  first | exact @GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | exact GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre | (intros; apply GlobalTheory.Ex.GenericFibre.fibre_eq_generic_fibre <;> assumption)
end

