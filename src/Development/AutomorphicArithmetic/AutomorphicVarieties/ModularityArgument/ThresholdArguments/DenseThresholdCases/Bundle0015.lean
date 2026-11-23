module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BFixOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndPtOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th
namespace UpperTheory.Gal.projectedFormsSystemPart
private theorem la_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A A' : ValuationSubring Ω} {w w' : W.Plc F} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (e : A = A')
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (ψ' : Fin n → Dec (F := F) A' →* (Qbar l)ˣ)
    (hψ : ∀ j (g : Dec (F := F) A) (g' : Dec (F := F) A'), (g : G F Ω) = (g' : G F Ω) → ψ j g = ψ' j g') (wt : Fin n → W.Emb l w → ℤ)
    (hm : ∀ τ, StrictMono fun j => wt j τ) (hl : ∀ j, W.IsLocAlg h (ψ j) (wt j)) :
    ∃ wt' : Fin n → W.Emb l w' → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧ ∀ j, W.IsLocAlg h' (ψ' j) (wt' j) := by
  subst e
  obtain rfl : w = w' := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))
  obtain rfl : ψ = ψ' := funext fun j => MonoidHom.ext fun g => hψ j g g rfl
  exact ⟨wt, hm, hl⟩
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}
def EndPtAlt (R : CReal k c₁ f 3 ka) (ι : Qbar l ≃+* ℂ) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) : Prop :=
  ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
    ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Arith h → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)
private theorem psi_eq (R : CReal k c₁ f 3 ka) {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ) (ξ : R.S.A →ₐ[c₁.O] Qbar l) (v) :
    W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) ((ξ.comp R.S.inc).comp φ) v = R.K.twψ (ptRep R.S ξ) v :=
  funext fun i => (TwLink.IsPhi.maps R.K hφ ξ).2 v i
private theorem off_self (R : CReal k c₁ f 3 ka) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ)
    {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J) (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l)
    (hV : VPt R.S ξ) (hTI : R.S.u.TI (RingHom.ker ξ)) (ha : W.UniversalOrdinaryDeterminantRing.Pt.Arith (B := R.B₀) ((ξ.comp R.S.inc).comp φ) h) :
    _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN R.s.v0 ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
  let ρ := R.K.tw (ptRep R.S ξ)
  let p : G L Ω →* R.V.frame.G₀ := R.V.pr
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D (B := R.B₀) ((ξ.comp R.S.inc).comp φ) = W.GDet.ofRep ρ :=
    (TwLink.IsPhi.maps R.K hφ ξ).1
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep (B := R.B₀) ((ξ.comp R.S.inc).comp φ) (ρ.toHomUnits.comp p) := by
    refine (congrArg (fun D : W.GDet 3 (Qbar l) R.V.frame.G₀ => D.comap p) hD).trans ?_
    change (W.GDet.ofRep ρ).comap p = W.GDet.ofRep (ρ.comp p)
    refine W.GDet.ext fun C _ _ y => ?_
    change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p y)).det =
      (W.GDet.repAlg (ρ.comp p) C y).det
    congr 1
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [W.GDet.repAlg]
  have hirr : Af.IsIrr (ρ.toHomUnits.comp p) := by
    have hMat := R.K.tw_irr _ (irrTI l c₁ _ R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hV.1 hTI)
    refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun U _ hU => hMat U fun g _ v hv => ?_⟩
    obtain ⟨t, rfl⟩ := Pr.pr_surj R.V g
    exact hU t v hv
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE ((ξ.comp R.S.inc).comp φ) h _
    (fun b hb => hg _ (RingHom.ker_isPrime _) hTI (Ideal.mem_map_of_mem φ hb)) ha hrep hirr
private theorem kap (R : CReal k c₁ f 3 ka) (g : G L Ω) : R.K.κA (Qbar l) (R.V.pr g) = ka g := Units.ext (R.κ_pr g)
private theorem psi_j (ρ : Fr.NRep (Φ.ext f) 3 (Qbar l)) {u u' : Φ.V} (e : u = u') (j : Fin 3) (a : Φ.Gv u) (a' : Φ.Gv u')
    (h : (k.j u a).1 = (k.j u' a').1) : ρ.ψ u j a = ρ.ψ u' j a' := by
  subst e
  rw [k.j_inj u (Subtype.ext h)]
theorem endPt_of_allGood_of_arithmeticPointClassicality (R R₀ : CReal k c₁ f 3 ka) (hp : ¬ R₀.s.p ∣ R.s.p) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B}
    (hφ : R.T.IsPhi φ) {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J)
    {φ' : R₀.B₀.B →ₐ[c₁.O] R.S.B} (hφ' : (setS R₀ R.S).T.IsPhi φ') {J' : Ideal R₀.B₀.B} (hg' : AllGood R.S (J'.map φ'))
    (hE' : R₀.B₀.arithmeticPointClassicalityDense ι J') : _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ := by
  rintro h ξ hV hTI _ rfl ha
  have key : ∀ v' : W.Vl l L, ∃ wt' : Fin 3 → W.Emb l (R₀.s.w v') → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧
      ∀ j, W.IsLocAlg (R₀.s.hw v') (W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R₀.B₀) ((ξ.comp R.S.inc).comp φ') v' j) (wt' j) := fun v' => by
    obtain ⟨v, hv⟩ : ∃ v : W.Vl l L, R.K.e v = R₀.K.e v' := R.K.e.surjective (R₀.K.e v')
    refine la_move (R.s.hw v) (R₀.s.hw v') ((R.A_pl v).trans ((congrArg k.pl hv).trans (R₀.A_pl v').symm)) _ _
      (fun j g g' e => ?_) (h v) (ha.1 v) (ha.2 v)
    rw [psi_eq R hφ ξ v, psi_eq (setS R₀ R.S) hφ' ξ v']
    change (ptRep R.S ξ).ψ (R.K.e v) j (R.K.lam v g) * R.K.κA (Qbar l) (R.V.pr g) =
      (ptRep R.S ξ).ψ (R₀.K.e v') j (R₀.K.lam v' g') * R₀.K.κA (Qbar l) (R₀.V.pr g')
    rw [kap, kap, e]
    exact congrArg (· * ka g') (psi_j (k := k) (ptRep R.S ξ) hv j (R.K.lam v g) (R₀.K.lam v' g')
      ((R.lam_j v g).trans ((congrArg (galEmb ℚ L Ω) e).trans (R₀.lam_j v' g').symm)))
  choose wt' h1 h2 using key
  have a := off_self R hφ hg hE h ξ hV hTI ha
  have b := off_self (setS R₀ R.S) hφ' hg' hE' wt' ξ hV hTI ⟨h1, h2⟩
  have e : ((setS R₀ R.S).K.tw (ptRep R.S ξ)).toHomUnits.comp (setS R₀ R.S).V.pr =
      (R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr := MonoidHom.ext fun g => Units.ext (by
    change ((R₀.K.κA (Qbar l) (R₀.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R₀.K.π (R₀.V.pr g)) =
      ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R.K.π (R.V.pr g))
    rw [kap, kap, R.π_pr, R₀.π_pr])
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (v0_ne hp) a (e ▸ b)
end
theorem niceAt2_alt :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ →
      R.S.u.TI (RingHom.ker ξ) → ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Good h →
      (Th.Free R.V.frame fun v => x.psi v) →
      _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits ∧ ∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R _ _ φ hφ hJ h ξ hV hTI x hx hGood hFree
  have hn : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  let ρQ : Fr.NRep (Φ.ext f) 3 (Qbar l) := ptRep R.S ξ
  let ρ0 : R.V.frame.G₀ →* GL (Fin 3) (Qbar l) := (R.K.tw ρQ).toHomUnits
  have hm : R.B₀.u.Maps ((ξ.comp (R.S.inc.comp φ) : R.B₀.B →ₐ[c₁.O] Qbar l) : R.B₀.B →+* Qbar l)
      (W.GDet.ofRep (R.K.tw ρQ)) (R.K.twψ ρQ) := TwLink.IsPhi.maps R.K hφ ξ
  have hxe : x = ξ.comp (R.S.inc.comp φ) := hx
  have hψ : ∀ v, x.psi v = R.K.twψ ρQ v := fun v => funext fun i => by
    rw [hxe]
    exact hm.2 v i
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D x = W.GDet.ofRep (R.K.tw ρQ) := by
    rw [hxe]
    exact hm.1
  have hcont : Continuous ρ0 := by
    have h1 : Continuous (R.K.tw ρQ) := by
      refine continuous_matrix fun a b => ?_
      have h2 := continuous_subtype_val.comp (((X.So.adicCont l c₁).2 _ _).1 R.K.κ_cont)
      have h3 := ((derRep l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 0 (Submodule.zero_mem _)).1 a b).comp R.K.π_cont
      exact h2.mul h3
    exact Units.continuous_iff.2 ⟨h1, h1.comp continuous_inv⟩
  have hirr : MatIrr ⊤ (W.mat ρ0) := R.K.tw_irr ρQ (irrTI l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 hTI)
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep x (ρ0.comp R.V.pr) := by
    let ρ := R.K.tw ρQ
    let p : G L Ω →* R.V.frame.G₀ := R.V.pr
    refine (congrArg (fun D => D.comap p) hD).trans ?_
    change (W.GDet.ofRep ρ).comap p = W.GDet.ofRep (ρ.comp p)
    refine W.GDet.ext fun C _ _ y => ?_
    change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p y)).det =
      (W.GDet.repAlg (ρ.comp p) C y).det
    congr 1
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [W.GDet.repAlg]
  have harith : W.UniversalOrdinaryDeterminantRing.Pt.Arith x h := ⟨hGood.1, fun v j => by
    obtain ⟨ph, hph, -⟩ := hGood.2 v
    exact ⟨ph j, hph j⟩⟩
  have hA : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ0 := by
    refine ⟨hcont, hrep, ⟨h, harith⟩, hJ h ξ hV hTI x hx harith, ?_, fun v => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : R.K.π (R.V.pr g) = 1 := by
        rw [R.π_pr]
        let A := R.s.A R.s.v0
        have valuation_lt_of_dvd {a b : ℕ} (hab : a ∣ b)
            (ha : A.valuation (a : Ω) < 1) : A.valuation (b : Ω) < 1 := by
          obtain ⟨d, rfl⟩ := hab
          rw [Nat.cast_mul, map_mul]
          exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A d))
        have hl : ¬ A.valuation (l : Ω) < 1 :=
          fun h' => R.v0M (valuation_lt_of_dvd ((dvd_mul_right l N).trans H.dvd) h')
        have hg' : galEmb ℚ L Ω g ∈ Ine (F := ℚ) A := hg
        have hc : cycZ ℚ Ω l (galEmb ℚ L Ω g) = 1 := (Base.places ℚ Ω l A).2.2.2 hl hg'
        have hd : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 :=
          (Chr.clsFacts ℚ Ω N).2.2.2.2 A
            (fun h' => R.v0M (valuation_lt_of_dvd ((dvd_mul_left N l).trans H.dvd) h')) hg'
        have hψg : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) = 1 := by
          simp [Chr.Psi, Chr.dirG, chiO, hc, hd]
        refine Subtype.ext ?_
        change toUpl Ω L (W.resP L Ω g) ∈ k.p.ker
        rw [k.p_ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hl, hg', ?_, ?_⟩)
        · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
        · exact (congrArg (Units.map (residue c.O).toMonoidHom) hψg).trans (map_one _)
      have h2 : R.K.κ (R.V.pr g) = 1 := R.K.ramκ _ ⟨g, hg, rfl⟩
      refine Units.ext ?_
      change ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • ρQ.r (R.K.π (R.V.pr g)) = 1
      have h3 : ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) = 1 := by
        change algebraMap c₁.O (Qbar l) ((R.K.κ (R.V.pr g) : (↥c₁.O)ˣ) : c₁.O) = 1
        rw [h2, Units.val_one, map_one]
      rw [h1, map_one, h3, one_smul]
    · rw [hψ v]
      obtain ⟨P, hP⟩ := Fr.flag R.ok hn R.S (Qbar l) (ξ : R.S.A →+* Qbar l) (R.K.e v)
      refine ⟨P, fun s => ?_⟩
      have entry (i j : Fin 3) : (P * (ρ0.comp (R.V.frame.φ v)) s * P⁻¹ : GL (Fin 3) (Qbar l)) i j =
          (R.K.κA (Qbar l) (R.V.frame.φ v s) : Qbar l) *
            (P * (ρQ.r.comp ((Φ.ext f).loc0 (R.K.e v))).toHomUnits (R.K.lam v s) * P⁻¹ : GL (Fin 3) (Qbar l)) i j := by
        change ((P : Matrix (Fin 3) (Fin 3) (Qbar l)) *
          ((R.K.κA (Qbar l) (R.V.frame.φ v s) : Qbar l) • ρQ.r (R.K.π (R.V.frame.φ v s))) *
          ((P⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l))) i j =
          _ * ((P : Matrix (Fin 3) (Fin 3) (Qbar l)) * ρQ.r ((Φ.ext f).loc0 (R.K.e v) (R.K.lam v s)) *
            ((P⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l))) i j
        rw [R.K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [entry, (hP _).1 i j hij, mul_zero]
      · rw [entry, (hP _).2 i, mul_comm]
        rfl
  have hVne : Nonempty Φ.V := by
    by_contra hV'
    rw [not_nonempty_iff] at hV'
    have h' : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h'
  obtain ⟨v'⟩ := hVne
  refine ⟨_root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 hn hA hirr hFree ?_, hψ⟩
  obtain ⟨v, hv⟩ := R.K.e.surjective v'
  obtain ⟨s, hs⟩ := R.ok.f3 (R.K.e v)
  obtain ⟨g, rfl⟩ := (R.K.lam v).surjective s
  refine ⟨v, 0, 1, g, fun h' => ?_⟩
  rw [R.K.psib, R.K.psib, R.K.chib, R.K.chib, ← R.K.lam_loc] at h'
  have hw : (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) ^ Fr.w 3 0 =
      (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) ^ Fr.w 3 1 := mul_right_cancel h'
  have hζ : (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) = 1 := by
    simpa [show Fr.w 3 0 = 1 by decide, show Fr.w 3 1 = 0 by decide] using hw
  exact hs (by rw [hζ, one_pow])
def Red2Alt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0
theorem red2_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt := by
  intro hG hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f ka R hW hK φ hPhi hSurj J hAll hDim hDense hEnd ξ hξ hTI a ha
  obtain ⟨h, hInc, hFree⟩ := wtEx hG Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hNice := _root_.UpperTheory.Gal.projectedFormsSystemPart.niceAt2_alt Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK φ hPhi hEnd h
  have hFix := _root_.UpperTheory.V.J.fixOf_alt hC Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hN : IsNoetherianRing R.B₀.B := IsCO.toIsNoetherian (O := c₁.O)
  have hD : DenseB R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) :=
    @denseOf l _ c₁ R.B₀.B R.S.B _ hN _ _ _ φ J (1 + 3 * (Φ.ext f).d) (fun x => W.UniversalOrdinaryDeterminantRing.Pt.Good x h) hSurj hDim (hDense h hInc)
  refine redAbs l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) hAll hD ?_ ξ hξ hTI (φ a) (Ideal.mem_map_of_mem _ ha)
  intro ζ hV hT _ hGd
  obtain ⟨h1, h2⟩ := hNice ζ hV hT _ rfl hGd (hFree _ hGd)
  exact fixLe l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ζ hV.1 hT (hFix ζ _ hV.1 h1 h2)
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRep
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
noncomputable section
open Polynomial Pointwise
namespace GlobalTheory.Ord2.SrcForm
open TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
theorem exists_rep_alt (P : _root_.UpperTheory.V.Af.Hypotheses') [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) (σ := s) hwl hA (q := 1) (fun x hx => by simpa only [pow_one] using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)
end GlobalTheory.Ord2.SrcForm
namespace GlobalTheory.Ord2
open TwDet SrcForm
end GlobalTheory.Ord2
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HostNumberS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut
namespace UpperTheory.V.UnitaryThreeInertia
def HostRigid_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r →
    (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) → F.Rigid r
def HostNumber_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∃ C : ℕ,
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∃ φ : Gam Ω S,
    (∀ r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → (_root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) →
      (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) ∧
    ∀ (n : ℕ) (r : Fin n → (Gam Ω S →* GG (m := 3) (R := PadicAlgCl l))),
      (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r i (toGS Ω _ s)).mat) →
      (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') →
      (∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace)) * Real.log l ≤ ((l : ℝ) * N * e) ^ C
end UpperTheory.V.UnitaryThreeInertia
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KapEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
def KapExAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (K' : IntermediateField ℚ Ω) [NumberField K'], l ≠ 2 → Module.finrank ℚ K' = 2 → IsTotallyComplex K' → ¬ (l : ℤ) ∣ discr K' →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) → (∃ cc : G ℚ Ω, Sd.IsCC cc) →
    ∃ (m : ℕ) (κ : G K' Ω →* (Qbar l)ˣ), ∀ j : ℕ, 1 ≤ j → KapDat ι K' (m * j) (κ ^ j)
end UpperTheory.V.Cu2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LemmaKOfLitN
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology
namespace UpperTheory.V.ZK
theorem lemmaK_of_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hB : BOdd) : ∃ CK, LemmaK CK :=
  lemmaK hB (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK
end UpperTheory.V.ZK
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedDvd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Lev.fixedDvd_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedDvdAlt
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedUnr
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
abbrev _root_.UpperTheory.V.Lev.fixedUnr_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedUnrAlt
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr
namespace UpperTheory.V.J
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}
end U
def ModNAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (r : Resid V.frame c.O 3), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.ModularAlt ι J Λ ∧ Num B Λ J
def IrrOpenAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (J : Ideal B.B), 1 ≤ n → B.arithmeticPointPurityDense ι J → ∀ x : B.Pt, IrrPt x →
    ∃ b₀ : B.B, x b₀ ≠ 0 ∧ ∀ (y : B.Pt) (w : s.Wt n), J ≤ RingHom.ker y → y.Good w → y b₀ ≠ 0 → IrrPt y
def UnramifiedEndsStatement : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → Num B Λ J → UnrAt B J
section Pt
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
  {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (ξ : R.S.R →ₐ[c₁.O] c₁.O)
end Pt
end UpperTheory.V.J
end
end
end

