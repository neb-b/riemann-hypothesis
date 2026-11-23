module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LanglandsMultisegmentsOfSeg
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellDec.TlComm

theorem tl_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  intro E _ _ n S ϖ l p hp
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (Matrix.GeneralLinearGroup.map c p = 1 ∨ Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1) = 1) →
      Matrix.GeneralLinearGroup.map c (p * GlobalTheory.CellDec.tl n ϖ l.1) =
        Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1 * p) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GlobalTheory.JSW.GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v ∈ S
    · refine Or.inr ?_
      rw [GlobalTheory.CellDec.tl, finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, GlobalTheory.SmGL.val_diagT]
      have hl : l.1 v = 0 := l.2 v hv
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq]
        show ((ϖ v ^ ((Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l.1) v) : (v.adicCompletion E)ˣ) :
          v.adicCompletion E) = 1
        rw [Finsupp.mapRange_apply, hl, Pi.zero_apply, zpow_zero, Units.val_one]
      · simp [Matrix.diagonal_apply, hij, Matrix.one_apply]
    · exact Or.inl (hp v hv)

end GlobalTheory.CellDec.TlComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

open Matrix

namespace GlobalTheory.CellDecNat

theorem glExt {E : Type} [Field E] [NumberField E] {n : ℕ} {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

theorem tl_eq_jsw_tl (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ))
    (h : ∀ w i, ((l' w i : ℕ) : ℤ) = l w i) : GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  classical
  unfold GlobalTheory.CellDec.tl GlobalTheory.JSW.tl
  have hm : (List.map (fun w => finGL E n (locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w)))) l'.support.toList).prod =
      finGL E n (List.map (fun w => locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w))) l'.support.toList).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hm]
  congr 1
  apply glExt
  intro w
  rw [map_list_prod, List.map_map,
    List.prod_map_eq_pow_single w _ (fun v hv _ => by simp only [Function.comp_apply]; exact pLoc_locGL_of_ne (Ne.symm hv) _)]
  simp only [Function.comp_apply, pLoc_locGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : ∀ i, (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w = ((l' w i : ℕ) : ℤ) := fun i => by
    rw [Finsupp.mapRange_apply, h]
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hw : w ∈ l'.support
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 hw), pow_one]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, zpow_natCast]
      simp [GlobalTheory.JSW.diagPow]
    · simp [Matrix.diagonal_apply_ne _ hij, GlobalTheory.JSW.diagPow]
  · rw [List.count_eq_zero_of_not_mem (by simpa using hw), pow_zero]
    have h0 : l' w = 0 := by simpa using hw
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, h0]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
end GlobalTheory.CellDecNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

namespace GlobalTheory.CoverBound

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0
    simp [InV, vV]
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV
    omega
  · intro h3
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h3
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_map_iff {T T' : CDVR} (i : T.Fr →+* T'.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) (x : T.Fr) : InV T' (i x) ↔ InV T x := by
  rw [inV_iff, inV_iff, hi]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast hr)

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {x : K} (hx : la.valuation K x ≤ 1) : InV T (io x) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : x = 0
  · simp [vLa, h0]
  have h2 := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  rw [WithZero.log_one] at h2
  unfold vLa
  omega

theorem inV_of_pow_eq (T : CDVR) {x : T.Fr} {e : ℕ} (he : 0 < e) (hx : x ^ (e + 1) = x) : InV T x := by
  by_cases h0 : x = 0
  · subst h0
    exact zero_mem (algebraMap T.V T.Fr).range
  have h := GlobalTheory.PlaceExtField.vV_pow (V := T.V) h0 (e + 1)
  rw [hx] at h
  rw [inV_iff]
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  push_cast at h
  have : (e : ℤ) * vV T.V x = 0 := by linarith
  exact ((mul_eq_zero.1 this).resolve_left he'.ne').ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem good_lift {X X₂ : Scheme.{0}} (t : SAB H X) (t₂ : SAB H X₂) (r : X₂ ⟶ X) (m : SABMap t₂ t r) (T T' : CDVR)
    (i : T.Fr →+* T'.Fr) (e : ℕ) (hi : ∀ a : T.Fr, vV T'.V (i a) = (e : ℤ) * vV T.V a) (x : Sp T.Fr ⟶ X)
    (x₂ : Sp T'.Fr ⟶ X₂) (hx : x₂ ≫ r = spMap i ≫ x)
    (h : ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' t x)
      (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom) :
    ∃ (G : SAB H (Sp T'.V)) (t' : SAB H (Sp T'.Fr)) (_ : SABMap t' t₂ x₂)
      (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), IsProper G.G.hom := by
  obtain ⟨G, t', m1, m2, hp⟩ := h
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceInt.Ext.exists_restrict T T' i e hi
  obtain ⟨G', ⟨mG⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ) G⟩⟩
  obtain ⟨s, ⟨n⟩⟩ : ∃ s : SAB H (Sp T'.Fr), Nonempty (SABMap s t' (spMap i)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap i) t'⟩⟩
  have hio : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← GlobalTheory.FramedBaseChange.spec_comp, ← GlobalTheory.FramedBaseChange.spec_comp]
    exact congrArg spMap (RingHom.ext fun a => (hφ a).symm)
  obtain ⟨a1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨a2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  rw [← hx] at a1
  rw [hio] at a2
  obtain ⟨b1, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m a1
  obtain ⟨b2, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG a2
  exact ⟨G', s, b1, b2, MorphismProperty.of_isPullback mG.cart.1 hp⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem shortValAt_of_map (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (β : c.F)
    (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {K k : Type} [Field K] [Field k] [Algebra c.F K] [Algebra c.F k]
    (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (z : FrPt Xo c k) (h : FrMap ψ y z) (v : K)
    (hv : ShortValAt Xo c nab w La β N P z (ψ v)) : ShortValAt Xo c nab w La β N P y v := by
  obtain ⟨S, _, _, φ, y', a, b, F, hf, hm, h1, h2, h3, h4, h5⟩ := hv
  refine ⟨S, inferInstance, inferInstance, φ.comp ψ, y', a, b, F, ?_, GlobalTheory.FramedBaseChange.trans ψ φ h hm,
    h1, h2, h3, h4, h5⟩
  haveI : Nontrivial S := hf.injective.nontrivial
  letI := (φ.comp ψ).toRingHom.toAlgebra
  exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem evR_pow_succ (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (e : ℕ) :
    evR Xo c (f ^ (e + 1)) y = evR Xo c f y ^ (e + 1) := by
  induction e with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ e ih => rw [pow_succ f, pow_succ (evR Xo c f y), ← ih]; exact evalAt_mul _ _ _ _ _


set_option maxHeartbeats 1000000 in
theorem bddAll_of_theta_sum_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n d N m : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (cs : Fin m → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : Fin m → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Dom a n → dδ.IsLev → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t q, la.valuation c.F (w t q) ≤ 1) → (∀ t, P t ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ∧ (P t).IsHomogeneous d ∧ ∀ k, la.valuation c.F ((P t).coeff k) ≤ 1) → f ∈ cusp Xo c U a n → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : Fin m → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → BddAll Xo c la (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw dδ.l₂) : ℕ) : c.F) * ((2 * NumberField.discr E * N : ℤ) : c.F) ^ d) f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hl _ a n d N m dδ La cs e w P f hdom hlev hnab hun htr hN he hcs hw hP hf
    hval
  refine _root_.GlobalTheory.GoodTransfer.bddAll_of_bddGood E H Dw l Xo c r U hU la p hp hpl hl a n f _ hdom hf ?_
  intro T io e₀ ho y hfin hgood
  have laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, -, hio₁, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c n dδ hlev T io y hfin
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra dδ.c₂.F T₁.Fr := io₁.toAlgebra
  obtain ⟨k, _, _, _, _, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T₁.Fr k)
      (_ : Algebra.IsAlgebraic T₁.Fr k), True :=
    ⟨AlgebraicClosure T₁.Fr, inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩
  letI ak : Algebra c.F k := ((algebraMap T₁.Fr k).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra dδ.c₂.F k := ((algebraMap T₁.Fr k).comp io₁).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  let ψ₂ : T₁.Fr →ₐ[dδ.c₂.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ _ _ ψ₂ z₁.1
  have hc1 : ∀ x : c.F, algebraMap dδ.c₂.F T₁.Fr (dδ.eF x) = algebraMap c.F T₁.Fr x := hio₁
  have hck : ∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x := fun x =>
    congrArg (algebraMap T₁.Fr k) (hio₁ x)
  have hoverk : FrOver dδ zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n dδ).2.1 T₁.Fr hc1 k hck ψ₁ ψ₂ rfl y₁.1 z₁.1 yk zk hover hyk hzk
  obtain ⟨v, hv, hev⟩ := hval k hck yk zk hoverk
  let K := IntermediateField.adjoin T₁.Fr (Set.range v)
  haveI : FiniteDimensional T₁.Fr K := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T₂, i₂, e₂, ρ, -, he₂, hv₂, hρ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ K
  obtain ⟨z₂, -, -, φ₂, hφ₂, hm₂⟩ :=
    (GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ T₁ T₂ io₁ z₁ i₂ e₂ he₂ hv₂).1
  letI b2 : Algebra dδ.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨j, hj, hjv⟩ : ∃ j : T₂.Fr →+* k, (∀ x, j (i₂ x) = algebraMap T₁.Fr k x) ∧ ∀ t, ∃ u, j u = v t := by
    refine ⟨(algebraMap K k).comp ρ.symm.toRingHom, fun x => ?_, fun t =>
      ⟨ρ ⟨v t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩, ?_⟩⟩
    · rw [← hρ]
      exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
    · exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
  choose u hu using hjv
  let χ : T₂.Fr →ₐ[dδ.c₂.F] k := { j with commutes' := fun x => hj (io₁ x) }
  have hχ : χ.comp φ₂ = ψ₂ := AlgHom.ext fun x => by
    show j (φ₂.toRingHom x) = algebraMap T₁.Fr k x
    rw [hφ₂, hj]
  have hm₃ : FrMap χ z₂.1 zk := GlobalTheory.FramedBaseChange.cancel φ₂ χ hm₂ (hχ ▸ hzk)
  have hv₀ : ∀ x : T.Fr, vV T₂.V ((i₂.comp i₁) x) = ((e₂ * e₁ : ℕ) : ℤ) * vV T.V x := fun x => by
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  have he₀ : 0 < e₂ * e₁ := Nat.mul_pos he₂ he₁
  have hgood₂ : Good z₂ := by
    refine good_lift Xo.univ.t dδ.Xo₂.univ.t dδ.r dδ.m T T₂ (i₂.comp i₁) _ hv₀ y.1.x z₂.1.x ?_ hgood
    rw [hm₂.1, Category.assoc, hover.1, hm₁.1, hφ₁, hφ₂, ← Category.assoc, ← GlobalTheory.FramedBaseChange.spec_comp]
  have hint : ∀ x : c.F, la.valuation c.F x ≤ 1 → InV T₂ ((i₂.comp io₁) (dδ.eF x)) := fun x hx => by
    rw [RingHom.comp_apply, hio₁]
    exact (inV_map_iff (i₂.comp i₁) he₀ hv₀ _).2 (inV_of_overLa ho hx)
  have hth := fun t => GlobalTheory.T.shortThetaValue_bounded_goodReduction E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ dδ.nab₂ hnab T₂ (i₂.comp io₁) z₂ n d N La
    (fun q => dδ.eF (w t q)) (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) (u t) hgood₂ hun htr hN
    (fun q => hint _ (hw t q)) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map _ (hP t).1) ((hP t).2.1.map _)
    (fun q => by rw [coeff_map]; exact hint _ ((hP t).2.2 q))
    (shortValAt_of_map _ _ _ _ _ _ χ z₂.1 zk hm₃ (u t) (by
      have h := hv t
      rw [← hu t] at h
      exact h))
  have e1 : evR Xo c f yk = (ψ₁.comp φ₁) (evR Xo c f y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 f
      (cusp_le_sec Xo c U a n hf).1 _ y.1 y.2.1 yk (GlobalTheory.FramedBaseChange.trans φ₁ ψ₁ hm₁ hyk)
  have e2 : ∀ t, evR dδ.Xo₂ dδ.c₂ (cs t) zk = j (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) := fun t =>
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂).2.2.1 (cs t) (hcs t).1.1 χ z₂.1
      z₂.2.1 zk hm₃
  have e3 : (i₂.comp i₁) (evI y f) = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1 * u t := by
    apply j.injective
    have e4 : j ((i₂.comp i₁) (evI y f)) = (ψ₁.comp φ₁) (evR Xo c f y.1) := by
      show j (i₂ (i₁ (evR Xo c f y.1))) = algebraMap T₁.Fr k (φ₁.toRingHom (evR Xo c f y.1))
      rw [hφ₁, hj]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e4, ← e1, hev, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul, e2, hu]
  rw [← inV_map_iff (i₂.comp i₁) he₀ hv₀, map_mul, e3, Finset.mul_sum]
  refine sum_mem (S := (algebraMap T₂.V T₂.Fr).range) fun t _ => ?_
  have h1 : InV T₂ (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) :=
    inV_of_pow_eq T₂ he (by rw [← evR_pow_succ, (hcs t).2])
  have h2 := mul_mem h1 (hth t)
  rw [map_mul, map_natCast, map_pow, map_intCast, map_mul, map_natCast, map_pow, map_intCast, mul_left_comm]
  exact h2

end GlobalTheory.CoverBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem conjPl_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem splitSet_of_split {S : Finset (Pl D.host.E)} (hs : ∀ P ∈ S, IsSplitPl D.host P)
    (hn : ∀ P ∈ S, ∀ P' ∈ S, ¬ IsConjPl D.host P P') : SplitSet S := by
  refine GlobalTheory.GridIdem.exists_isIdemSum S (fun P hP => GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conjPl_ne_of_split (hs P hP)))
    fun P hP P' hP' h => ?_
  rcases (GlobalTheory.Mem.TypePl.under_eq_iff P P').1 h.symm with e | e
  · exact e.symm
  · exact absurd e (hn P hP P' hP')

end GlobalTheory.UnivGood

namespace GlobalTheory.UnivGood

variable {D : D7}

theorem univOf_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ),
      (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).Good (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) := by
  intro D N X ρ hρ Y i Q M
  classical
  set A := admissibleConjugatePairPlaces X i Q M with hA
  have hAconj : ∀ P ∈ A, ∀ P', IsConjPl D.host P P' → P' ∈ A := fun P hP P' hc => conj_mem_admissibleConjugatePairPlaces hP hc
  have hsplit : SplitSet (half (ρ.ch i) A) := by
    refine splitSet_of_split (fun P hP => isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces (mem_half.1 hP).1) hc
    exact ((hρ.ch i).pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  refine ⟨hsplit, fun PP hPP => ?_⟩
  have hPA : PP ∈ A := (mem_half.1 hPP).1
  obtain ⟨-, P', hP'Q, hc, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPA
  have hP'A : P' ∈ A := conj_mem_admissibleConjugatePairPlaces hPA hc
  set φ := coord Y i A M PP with hφ
  have hco : ∀ σ, Multiplicative.toAdd (φ σ) = Multiplicative.toAdd (Y.delU i A M σ) ⟨PP, hPA⟩ :=
    fun σ => coord_apply Y i A M hPA σ
  have hord : ∀ σ, ∃ n : ℕ, φ σ ^ (X.l i ^ n) = 1 := fun σ => ⟨M, by
    rw [← ofAdd_toAdd (φ σ), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]⟩
  have hopen : IsOpen (φ.ker : Set (G D.host.E N.Om)) := by
    refine Subgroup.isOpen_mono (H₁ := (Y.delU i A M).ker) (fun g hg => ?_) (Y.delU_open i A M)
    refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
    rw [hco, MonoidHom.mem_ker.1 hg]
    rfl
  have hanti : AntiHom X.cc φ := fun g g' hg => by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_inv, hco, hco, Y.delU_anti i A M g g' hg, toAdd_inv]
    rfl

  have hpair : ∀ x ∈ ({PP, P'} : Finset (Pl D.host.E)), ∀ y, IsConjPl D.host x y → y ∈ ({PP, P'} : Finset (Pl D.host.E)) := by
    intro x hx y hy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [GlobalTheory.GalChar.isConjPl_unique hy hc]; simp
    · rw [Finset.mem_singleton] at hx
      subst hx
      rw [GlobalTheory.GalChar.isConjPl_unique hy (GlobalTheory.GalChar.isConjPl_symm hc)]; simp
  have hsub : ({PP, P'} : Finset (Pl D.host.E)) ⊆ A := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hPA
    · rw [Finset.mem_singleton] at hx; subst hx; exact hP'A
  have hunr : ∀ v : Pl D.host.E, v ∉ ({PP} : Finset (Pl D.host.E)) →
      (∀ P ∈ ({PP} : Finset (Pl D.host.E)), ¬ IsConjPl D.host P v) →
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1 := by
    intro v hv hnc B hB σ hσ
    have hv' : v ∉ ({PP, P'} : Finset (Pl D.host.E)) := by
      intro h
      rcases Finset.mem_insert.1 h with rfl | h
      · exact hv (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton] at h
        subst h
        exact hnc PP (Finset.mem_singleton_self _) hc
    refine Multiplicative.toAdd.injective ?_
    rw [hco, ← Y.delU_res i M {PP, P'} A hsub hpair hAconj σ PP (by simp),
      Y.delU_unr i {PP, P'} M v hv' B hB σ hσ]
    rfl
  have hl : ∀ P ∈ ({PP} : Finset (Pl D.host.E)), ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact (hadm.1 P (by simp)).2
  have hg := GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc (Multiplicative (ZMod (X.l i ^ M))) φ (X.l i) (X.lPrime i).out hord hopen
    hanti {PP} (hsplit.mono (Finset.singleton_subset_iff.2 hPP)) hl hunr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  refine ⟨h1, h2, h3, h4, h5, fun P hP => ?_⟩
  rw [Finset.mem_singleton] at hP
  subst hP
  exact h6 _ (Finset.mem_singleton_self _)

end GlobalTheory.UnivGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  first | (exact @GlobalTheory.JSW.WhitCont.continuous_whit) | (exact GlobalTheory.JSW.WhitCont.continuous_whit) | (intros; apply GlobalTheory.JSW.WhitCont.continuous_whit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrothendieckRingPolynomialOutright
section
namespace GlobalTheory

theorem grothendieckRingPolynomial_outright : GlobalTheory.Published.GrothendieckRingPolynomial :=
  CompanionTheory.Groth.grothendieckRingPolynomial_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

