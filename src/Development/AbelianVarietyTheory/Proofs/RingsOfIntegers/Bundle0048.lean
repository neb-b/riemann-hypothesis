module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_similitude_data_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  first | exact @GlobalTheory.PlaceInt.AdaptExists.exists_adapt | exact GlobalTheory.PlaceInt.AdaptExists.exists_adapt | (intros; apply GlobalTheory.PlaceInt.AdaptExists.exists_adapt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace NormPullUniq

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_unique (hp : Function.Surjective A.hom.appTop.hom) (φ : A ⟶ A) (a b : ℤ)
    {T : Over S} {s : LB.Sec (LPow A L.L b T)} {s₁ s₂ : LB.Sec (LPow A L.L a T)}
    (h₁ : IsNormPull A L φ a b s s₁) (h₂ : IsNormPull A L φ a b s s₂) : s₁ = s₂ := by
  have hL := L.isLB
  obtain ⟨α₀, α, hα₀, nα, cα, tα⟩ := h₁
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h₂
  have key : ∀ j, s₁.f j = s₂.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s := s₁) (s' := s₂)
      fun y J hJ => by
        refine (twist_val tα (𝟙 _) y hJ).trans (Eq.trans ?_ (twist_val tβ (𝟙 _) y hJ).symm)
        rw [val_corr hJ cα (𝟙 _), val_corr hJ cβ (𝟙 _), val_pull hJ, val_pull hJ]
        rw [gen_unique hL A.hom (eSec A) NormMulUniv.eSec_hom hp hα₀ hβ₀ (fun w I hI => by
          have a := val_corr hI nα (𝟙 _)
          have b := val_corr hI nβ (𝟙 _)
          rw [val_pull hI, Category.id_comp] at a b
          exact a.trans b.symm) _ _ y J hJ]
  obtain ⟨f₁, p₁⟩ := s₁
  obtain ⟨f₂, p₂⟩ := s₂
  obtain rfl : f₁ = f₂ := funext key
  rfl

end NormPullUniq

theorem existsUnique_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ F : SecN Xo x k, ∃! F' : SecN Xo x k', Pulls Xo a F F' := by
  intro E _ _ _ H Dw l Xo S _ x a N k k' ha hk F
  subst hk
  letI := H.starRing
  have := Xo.univ.t.act.hom a
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 a N ha (Xo.univ.t.adj a)
    Xo.univ.t.prim k
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act a).left]
    ![((k * N : ℕ) : ℤ), -(k : ℤ)] rfl
  obtain ⟨F', hF'⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act a) ((k * N : ℕ) : ℤ) k β hβ F
  exact ⟨F', hF', fun F'' hF'' => NormPullUniq.isNormPull_unique Xo.univ.t.PP
    (SemiRigid.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 _ _ _ hF'' hF'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermSymmetricTranslateFibreEqModel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransportGerm
open GlobalTheory.RegularGerm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

omit [StarRing (𝓞 E)] in
theorem base₁ (y : IntFr Xo c T io) :
    (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ (ptO Xo (xOf y)).hom =
      (baseOver (Sp T.Fr)).hom ≫ xOf y := rfl

theorem base₂ (T : CDVR) :
    (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ (baseOver (Sp T.V)).hom =
      (baseOver (Sp T.Fr)).hom ≫ spMap (algebraMap T.V T.Fr) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

def RelFibre (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (F : SecN Xo (xOf y) k) : Prop :=
  ThetaPtMove.SecRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.w1 s F

def RelModel (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))) : Prop :=
  ThetaPtMove.SecRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.w2 s σ


set_option maxHeartbeats 1600000 in
theorem germIs_of_rel (hFT : ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c) (C : IntegralChartA3 Xo c T io y) {k : ℕ}
    {s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr)))} {F : SecN Xo (xOf y) k}
    {σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))} (h₁ : RelFibre C s F) (h₂ : RelModel C s σ)
    {g : PS T.V 1 (chD C.ch)} (hg : IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ g) :
    GermIs C k F g := by
  letI := io.toAlgebra
  obtain ⟨x', hx1, hx2, eL', heL'⟩ := hFT T io y C
  refine (isGerm_iff y.1 _ _ _ _ _ _ _ _).2
    (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)
  obtain ⟨J', hJ', -⟩ := exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J'', hJ'', -⟩ := exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  let ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m) :=
    spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)
  let i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) := 𝟙 _
  obtain ⟨f₁, f₂⟩ := heL' m _ i z J J' J'' hJ hJ' hJ''
  have a₁ := h₁ _ (i ≫ jetPt (x' m)) z J J' hJ hJ'
  have a₂ := h₂ _ (i ≫ jetPt (x' m)) z J'' J' hJ'' hJ'
  have a₃ := sv_of_isGerm hg m (i ≫ ρ) z hJ''
  have e₀ : (i ≫ jetPt (x' m)) ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left = i ≫ (x' m).left :=
    (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (jetPt_snd (x' m)))
  have e₁ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) = i ≫ jetPt (C.ch.x m) := by
    refine (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((congrArg (_ ≫ ·) (Category.comp_id _)).trans ((jetPt_fst (x' m)).trans (jetPt_fst (C.ch.x m)).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx1 m).trans (jetPt_snd (C.ch.x m)).symm))))
  have e₂ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) = (i ≫ ρ) ≫ jetPt (C.xT m) := by
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_)).trans
      (Category.assoc _ _ _).symm)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_fst (x' m))).trans
          (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_fst (C.xT m)))).symm))))
      have q := congrArg (· ≫ C.I.G.G.hom) (hx2 m)
      have q₁ : (x' m).left ≫ C.I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (x' m)).trans (Category.comp_id _)
      have q₂ : (C.xT m).left ≫ C.I.G.G.hom = spMap (algebraMap T.V (Jet T.V (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (C.xT m)).trans (Category.comp_id _)
      exact (congrArg (· ≫ _) q₁).symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) C.I.m2.cart.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
          (q.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) q₂))))))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx2 m).trans ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_snd (C.xT m)))).symm))))
  rw [e₀, e₁, zpow_natCast, Units.val_pow_eq_pow_val] at a₁
  rw [e₀, e₂, zpow_natCast, Units.val_pow_eq_pow_val] at a₂
  rw [Category.comp_id] at f₁ f₂
  refine (tie_alg a₁ a₂ a₃ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [psJet_map]
  exact gs_spMap_toΓ _ i z _


set_option maxHeartbeats 800000 in
theorem exists_rel (C : IntegralChartA3 Xo c T io y) {k : ℕ} {F : SecN Xo (xOf y) k} (hF : Regular C k F) :
    ∃ s σ, RelFibre C s F ∧ RelModel C s σ := by
  letI := io.toAlgebra
  obtain ⟨σ, σt, hT1, hT2⟩ := hF
  obtain ⟨σ', hσ'⟩ := exists_sec_id C.I.G (k : ℤ) σ (baseOver (Sp T.V))
  obtain ⟨s, hs⟩ := exists_sec_id C.I.t' (k : ℤ) σt (baseOver (Sp T.Fr))
  refine ⟨s, σ', fun Z r z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · have q := hT1 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left)
      (r ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        (Category.assoc _ _ _).symm))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((ThetaPtMove.psi_fst' _ _ _).trans
        ((Over.w (fst (baseOver (Sp T.Fr)) C.I.t'.G)).trans (Over.w (snd (baseOver (Sp T.Fr)) C.I.t'.G)).symm))).trans
          (Category.assoc _ _ _).symm)) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    exact q
  · have q := hT2 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    refine (hσ' Z _ z J hJ).trans (Eq.trans (congrArg (fun p => sval σ p z J) ?_) q)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
      (Category.assoc _ _ _).symm)


set_option maxHeartbeats 800000 in
theorem germIs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ), Odd k → ∀ (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (aV : baseOver (Sp T.V) ⟶ C.I.G.G) (r : Sp T.Fr ⟶ C.I.t'.G.left), r ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = a.left → r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV.left → ∀ U : ThetaGrp C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)), SymLift C.I.G.G C.I.G.PP.L (k : ℤ) k aV U → ∀ (F F' : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → (∀ σ σ' : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V))), IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ f → IsActOf C.I.G.G C.I.G.PP.L (k : ℤ) U σ σ' → IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ' f') → GermIs C k F' f' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC k hk a aV r hr hr1 hr2 U hU F F' f f' hF hf hM hyp
  letI := io.toAlgebra
  have hFT := GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar
  have hA : IsAbelianScheme C.I.t'.G := isAbelianScheme_of_pullback_univ E H Dw l Xo _ C.I.t' _ C.I.m1
  obtain ⟨hak, U₀, hU₀, hact⟩ := hM
  obtain ⟨s, σ, h₁, h₂⟩ := exists_rel C hF
  obtain ⟨g, hg⟩ := germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT
    (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT
    C.chartT C.frameT C.primT hC k σ
  obtain rfl : g = f := germIs_unique C k F _ _ (germIs_of_rel hFT C h₁ h₂ hg) hf
  obtain ⟨σ', hσ', -⟩ := existsUnique_isTwistPull _ _ _ C.I.G.PP.isLB _ (translT _ U.pt) (translPt _ U.pt)
    (lift_snd _ _) k k U.φ U.isGen σ
  let x : baseOver (Sp T.Fr) ⟶ C.I.t'.G := Over.homMk r hr
  have hx₁ : (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ a.left = x.left ≫ C.I.m1.φ :=
    (Category.id_comp _).trans hr1.symm
  have hx₂ : (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ aV.left =
      x.left ≫ C.I.m2.φ := hr2.symm
  have hn : x ^ k = 1 := by
    refine Over.OverMorphism.ext (C.I.m1.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have p := ThetaPtMove.over_pow (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) hx₁ k
    rw [hak] at p
    exact p.symm.trans (ThetaPtMove.over_one (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
  obtain ⟨θ₁, l₁, m₁⟩ := ThetaPtMove.symLift_move (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB hx₁ hn hU₀
  obtain ⟨θ₂, l₂, m₂⟩ := ThetaPtMove.symLift_move C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB hx₂ hn hU
  obtain ⟨s₁, r₁⟩ := ThetaPtMove.exists_secRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB F'
  obtain ⟨s₂, r₂⟩ := ThetaPtMove.exists_secRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB σ'
  obtain rfl : s₁ = s₂ := SymMove.act_unique firstFiveLaws.1.globalFns hA C.I.t'.PP.isLB hk l₁ l₂
    (m₁ _ _ _ _ h₁ r₁ hact) (m₂ _ _ _ _ h₂ r₂ hσ')
  exact germIs_of_rel hFT C r₁ r₂ (hyp σ σ' hg hσ')

end GlobalTheory.TransportGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortUnits

open GlobalTheory.LatticeIndex GlobalTheory.TrivLattice

section Val
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem valuation_nat {k : ℕ} (hk : (k : 𝓞 K) ∉ la.asIdeal) : la.valuation K (k : K) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 K) K)]
  exact la.valuation_eq_one_iff_notMem.2 hk

theorem not_mem_of_coprime' {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) :
    (b : 𝓞 K) ∉ la.asIdeal := fun hb => by
  obtain ⟨u, v, e⟩ : IsCoprime (a : 𝓞 K) (b : 𝓞 K) := h.cast
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ ha) (la.asIdeal.mul_mem_left _ hb)))

end Val

theorem vLa_beta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (la : HeightOneSpectrum (𝓞 c.F)) (hA : PullbackSections.AdaptAt Λ la) (β : c.F)
    (hβ : BetaIs (Dw := Dw) c Λ β) : vLa la β = 0 := by
  obtain ⟨k, hk, hk1, hk2⟩ := hA
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  let w := la.valuation c.F
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hw ⟨_, map_isIntegral_int (embF c τ) r.isIntegral_coe⟩
  have hnat : ∀ τ, w.comap (embF c τ) (k : E) = 1 := fun τ => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valuation_nat la hk
  have hm : ∀ (A : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := fun A a1 a2 => by
    have := hasMax_prod hw Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) fun τ => by
      obtain ⟨a, y, hy, b⟩ := detSet_max _ (hwτ τ) A (hnat τ) a1 a2
      have h : HasMax w (idealAt c A τ) 1 := by
        refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
        rintro _ ⟨y, hy, rfl⟩
        exact a y hy
      simpa using h.pow hw (Dw.mult τ)
    simpa using this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {β}) (w β) := hasMax_span hw (by simp) (by simp)
  have f1 := hb.mul (hm Λ.La h1 h2)
  rw [hβ] at f1
  have f := f1.unique (hm Λ.Ln (fun v hv => h1 v hv.1)
    (fun v hv => ⟨h2 v hv, (stdLat E n).toAddSubgroup.nsmul_mem hv k⟩))
  rw [_root_.mul_one] at f
  have f' : la.valuation c.F β = 1 := f
  simp [vLa, f']

theorem vLa_betaH {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ} (Λ : GenLat D.host.E n)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D)) (hA : PullbackSections.AdaptAt Λ la) :
    vLa la (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 0 := by
  have h := hF.sh.beta j hj n (hF.p.kPsi j hj) Λ hU hT
  refine vLa_beta (Dw := T.Q.Dw j) T.Q.c Λ la hA _ ?_
  unfold betaH
  rw [dite_eq_left h]
  exact h.choose_spec.2.1

end GlobalTheory.ShortUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTorsionTranslateSectionNuNonneg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.PlaceInt

theorem zero_le_val_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (hu : u ^ m = 1) : ((0 : ℚ) : WithTop ℚ) ≤ v u := by
  have h : m • v u = 0 := by rw [← v.map_pow, hu, v.map_one]
  cases hc : v u with
  | top => exact le_top
  | coe q =>
    rw [hc, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h
    rcases h with h | h
    · omega
    · rw [h]

theorem nuGe_zero_of_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh hh' : SecN Xo xF k), 1 ≤ k → Moves Xo b hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k σ hh' → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k b hh hh' hk hmv hν σ' s' hσ' hs'
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have h3 : FiniteOrderValuationInvariance := (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.1
  have hx := hσ'.base
  obtain ⟨⟨σ, hσ, -⟩, hex⟩ := _root_.GlobalTheory.tied_section_expansion_existsUnique E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh
  obtain ⟨s, hs, -⟩ := hex σ hσ
  obtain ⟨s₁, -, hu'⟩ := (_root_.GlobalTheory.tied_section_expansion_existsUnique E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh').2 σ' hσ'
  obtain ⟨e, he, -⟩ := GlobalTheory.PtTie.exists_mulEquiv_ptTieF E H Dw l Xo c T io y.1 I P F xF hx
  have hxk : (e.symm b) ^ k = 1 := by rw [← map_pow, hmv.1, map_one]
  obtain ⟨f, hf, hsurj, -⟩ := hT F k hk
  obtain ⟨p, hp⟩ := hsurj _ hxk
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen :=
    ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := ReciprocityTheory.ChartRestriction.G.H1.finOrdExists_of_laws hL T.V P.D F k hk p w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V (maximalIdeal T.V) P.D F k hk p w hw
  have h1 : PhiRel P.D.toPre F k p w s (Φ s) := (hΦ _ _).2 rfl
  have h2 : Fam.IsSmul P.D.toPre F ζ (Φ s) (ζ • Φ s) := (ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, ht'⟩ := GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y.1 I P F xF hx k hk σ σ' hh hh' s (Φ s) (ζ • Φ s)
    (e.symm b) b p w ζ hσ hσ' hs hmv ((he _ _).2 (e.apply_symm_apply b).symm) ((hf _ _).2 hp.symm) hw hfin h1 h2
  have h4 := (h3 T.V ϖ hϖ P.D Q hQ F v hv k hk p w hw ζ hζ hfin s _ _ h1 h2 0).1 (hν σ s hσ hs)
  have h5 := NuGe.smul Q (zero_le_val_of_pow_eq_one v hm hum) hut h4
  rw [add_zero] at h5
  rw [hu' s' hs', ← hu' t' ht']
  exact h5

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslateMulOfCoprimeOrders
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem weilIs_eq_one_of_coprime (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (hk : IsUnit (k : Γ(T.left, ⊤))) (a b : T ⟶ P.A) (m m' : ℕ) (ha : a ^ k = 1) (hb : b ^ k = 1)
    (hc : Nat.Coprime m m') (ham : a ^ m = 1) (hbm : b ^ m' = 1) (e : Γ(T.left, ⊤)ˣ)
    (he : WeilIs P.A P.L k a b e) : e = 1 := by
  have h₁ : e ^ m = 1 := by
    obtain ⟨hex, hmul, -, -⟩ := hW S P k T
    obtain ⟨c₁, hc₁, hu⟩ := hex 1 b (one_pow k) hb
    have h₂ := hmul 1 1 b c₁ c₁ hc₁ hc₁
    rw [_root_.mul_one] at h₂
    obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
    have hpow : ∀ j : ℕ, WeilIs P.A P.L k (a ^ j) b (e ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero, pow_zero]; exact hc₁
      | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih he
    have h := hpow m
    rw [ham] at h
    exact hu _ h
  have h₂ : e ^ m' = 1 := by
    have hbg : b ^ Nat.gcd k m' = 1 := pow_gcd_eq_one.2 ⟨hb, hbm⟩
    obtain ⟨n, hn⟩ := Nat.gcd_dvd_left k m'
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_right k m'
    generalize Nat.gcd k m' = g at hbg hn hn'
    subst hn
    have h := ((hW S P g T).2.2.2 n a b e hk ha hbg).1 (by exact_mod_cast he)
    have hg := GlobalTheory.UnivPairing.weilIs_pow_eq_one hW P g (a ^ n) b (by rw [← pow_mul, mul_comm]; exact ha) hbg e h
    rw [hn', pow_mul, hg, one_pow]
  have h := pow_gcd_eq_one.2 ⟨h₁, h₂⟩
  rwa [hc.gcd_eq_one, pow_one] at h

theorem moves_mul_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (m m' : ℕ), a ^ k = 1 → b ^ k = 1 → Nat.Coprime m m' → a ^ m = 1 → b ^ m' = 1 → ∀ F F₁ F₂ : SecN Xo x k, Moves Xo b F F₁ → (Moves Xo a F₁ F₂ ↔ Moves Xo (a * b) F F₂) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b m m' ha hb hc ham hbm F F₁ F₂ h₁
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  have := UnivPol.isLocallyNoetherian Xo
  have hu : IsUnit (k : Γ((ptO Xo x).left, ⊤)) := by
    have h := (UnivPol.isUnit_natCast Xo k hk.pos).map (ptO Xo x).hom.appTop.hom
    rwa [map_natCast] at h
  obtain ⟨e, he, -⟩ := (hW Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 a b ha hb
  have he1 : e = 1 := weilIs_eq_one_of_coprime hW (UnivPol.pol Xo) k hu a b m m' ha hb hc ham hbm e he
  obtain ⟨r, hr2, hrk, hr⟩ := GlobalTheory.PlaceInt.moves_mul E H Dw l Xo S x k hk a b e ha hb he
  have hr1 : toΓ S r = 1 := by
    rw [he1, Units.val_one] at hr2
    have h3 : toΓ S r ^ k = 1 := by rw [← map_pow, hrk, map_one]
    obtain ⟨n, rfl⟩ := hk
    rwa [pow_succ, pow_mul, hr2, one_pow, _root_.one_mul] at h3
  have key : ∀ G G' : SecN Xo x k, Moves Xo a F₁ G → Moves Xo (a * b) F G' → G = G' := by
    intro G G' hG hG'
    have h := hr F F₁ G G' h₁ hG hG'
    have h' : G.f = G'.f := funext fun j => by
      rw [h j, hr1]
      unfold liftFun
      rw [map_one, map_one, _root_.one_mul]
    cases G
    cases G'
    cases h'
    rfl
  have hab : (a * b) ^ k = 1 := by rw [mul_pow, ha, hb, _root_.mul_one]
  constructor
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk (a * b) hab F).1
    rw [key F₂ G h hG]
    exact hG
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk a ha F₁).1
    rw [← key G F₂ hG h]
    exact hG

end GlobalTheory.PlaceInt
end

