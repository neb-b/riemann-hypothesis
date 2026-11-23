module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
section
open NumberField

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen
variable {R : Type} [CommRing R]

theorem card_torsion_eq {A : Type} [AddCommGroup A] [Module R A] [Finite A] {c π : R} {J : Ideal R}
    (hJ : Ideal.span {c} ⊔ Ideal.span {π} = J) (hc : ∀ x : A, c • x = 0) :
    Nat.card (Submodule.torsionBySet R A (J : Set R)) = Nat.card (A ⧸ J • (⊤ : Submodule R A)) := by
  let f : A →ₗ[R] A := π • LinearMap.id
  have hmem : ∀ a ∈ J, ∃ r s : R, a = r * c + s * π := by
    intro a ha
    rw [← hJ, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨r, s, rfl⟩
  have hπ : π ∈ J := hJ ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self π)
  have h1 : Submodule.torsionBySet R A (J : Set R) = LinearMap.ker f := by
    ext x
    rw [Submodule.mem_torsionBySet_iff, LinearMap.mem_ker]
    constructor
    · intro h; simpa [f] using h ⟨π, hπ⟩
    · rintro h ⟨a, ha⟩
      obtain ⟨r, s, rfl⟩ := hmem a ha
      have h' : π • x = 0 := by simpa [f] using h
      simp only [add_smul, mul_smul, hc, h', smul_zero, add_zero]
  have h2 : J • (⊤ : Submodule R A) = LinearMap.range f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro a ha n _
      obtain ⟨r, s, rfl⟩ := hmem a ha
      refine ⟨s • n, ?_⟩
      change π • (s • n) = _
      rw [add_smul, mul_smul, hc, smul_zero, zero_add, mul_smul, smul_comm]
    · rintro _ ⟨y, rfl⟩
      simpa [f] using (Submodule.smul_mem_smul hπ (Submodule.mem_top : y ∈ (⊤ : Submodule R A)))
  rw [h1, h2]
  have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at e1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [e1, mul_comm] at e2
  exact Nat.eq_of_mul_eq_mul_left hpos e2

end Gen
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
section Sub
variable {R : Type} [CommRing R] {A : Type} [AddCommGroup A] [Module R A] (J : Ideal R)

def toQ (S : Submodule R (Submodule.torsionBySet R A (J : Set R))) :
    Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    show (algebraMap R (R ⧸ J) r) • x ∈ S
    rw [algebraMap_smul]
    exact S.smul_mem r hx

theorem card_sub_eq (m : ℕ) :
    Nat.card {T : Submodule R A // T ≤ Submodule.torsionBySet R A (J : Set R) ∧ Nat.card T = m} =
      Nat.card {S : Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) // Nat.card S = m} := by
  set V := Submodule.torsionBySet R A (J : Set R)
  have cardT : ∀ T : Submodule R A, T ≤ V → Nat.card (toQ J (T.comap V.subtype)) = Nat.card T := fun T hT =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hT y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have cardS : ∀ S : Submodule (R ⧸ J) V, Nat.card ((S.restrictScalars R).map V.subtype) = Nat.card S := fun S =>
    (Nat.card_congr (Submodule.equivMapOfInjective V.subtype V.injective_subtype (S.restrictScalars R)).toEquiv).symm
  refine Nat.card_congr
    { toFun := fun T => ⟨toQ J (T.1.comap V.subtype), (cardT T.1 T.2.1).trans T.2.2⟩
      invFun := fun S => ⟨(S.1.restrictScalars R).map V.subtype, fun _ ⟨x, _, hx⟩ => hx ▸ x.2,
        (cardS S.1).trans S.2⟩
      left_inv := fun T => ?_
      right_inv := fun S => ?_ }
  · apply Subtype.ext
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨⟨y, T.2.1 hy⟩, hy, rfl⟩
  · apply Subtype.ext
    ext x
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := Subtype.ext h
      exact this ▸ hx'
    · intro hx; exact ⟨x, hx, rfl⟩

end Sub
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pSub (D : Datum H) (p : ℕ) : Submodule (𝓞 E) D.La := Ideal.span {(p : 𝓞 E)} • ⊤

theorem mem_pSub {D : Datum H} {p : ℕ} {x : D.La} : x ∈ pSub D p ↔ x ∈ pLat D p := by
  rw [pSub, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, mem_pLat]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

def asSub {D : Datum H} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    Submodule (𝓞 E) D.La where
  toAddSubmonoid := N.toAddSubmonoid
  smul_mem' a x hx := hN a x hx

theorem relIndex_eq_card {D : Datum H} {p : ℕ} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    (pLat D p).relIndex N = Nat.card ((asSub N hN).map (pSub D p).mkQ) := by
  let g : D.La →+ D.La ⧸ pSub D p := (pSub D p).mkQ.toAddMonoidHom
  have hker : g.ker = pLat D p := by
    ext x
    rw [AddMonoidHom.mem_ker, ← mem_pSub]
    exact Submodule.Quotient.mk_eq_zero _
  rw [← hker, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  rfl

def latEquiv (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) :
    LatCount D p J m ≃ {T : Submodule (𝓞 E) (D.La ⧸ pSub D p) //
      T ≤ Submodule.torsionBySet (𝓞 E) (D.La ⧸ pSub D p) (J : Set (𝓞 E)) ∧ Nat.card T = m} where
  toFun N := ⟨(asSub N.1 N.2.2.1).map (pSub D p).mkQ, by
      rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_pSub]
      exact N.2.2.2.1 a ha x hx,
    (relIndex_eq_card N.1 N.2.2.1).symm.trans N.2.2.2.2⟩
  invFun T := ⟨(T.1.comap (pSub D p).mkQ).toAddSubgroup,
    fun x hx => by
      show (pSub D p).mkQ x ∈ T.1
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (mem_pSub.2 hx)]
      exact T.1.zero_mem,
    fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx,
    fun a ha x hx => by
      have h := (Submodule.mem_torsionBySet_iff _ _).1 (T.2.1 hx) ⟨a, ha⟩
      rw [← mem_pSub, ← Submodule.Quotient.mk_eq_zero]
      exact ((pSub D p).mkQ.map_smul a x).trans h,
    by
      refine (relIndex_eq_card _ (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).trans (Eq.trans ?_ T.2.2)
      have e : (asSub (T.1.comap (pSub D p).mkQ).toAddSubgroup
          (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).map (pSub D p).mkQ = T.1 :=
        Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _
      rw [e]⟩
  left_inv N := by
    apply Subtype.ext
    ext x
    show (pSub D p).mkQ x ∈ (asSub N.1 N.2.2.1).map (pSub D p).mkQ ↔ x ∈ N.1
    constructor
    · rintro ⟨y, hy, h⟩
      have h' : y - x ∈ pSub D p := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        exact sub_eq_zero.2 h
      have := N.1.sub_mem hy (N.2.1 (mem_pSub.1 h'))
      simpa using this
    · intro hx; exact ⟨x, hx, rfl⟩
  right_inv T := Subtype.ext (Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _)

end Lat
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

theorem card_latCount : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  intro E _ _ _ H Dw p J hp hJ hpJ k
  haveI := Dw.fin
  haveI := Dw.proj
  letI := Ideal.Quotient.field J
  set R := 𝓞 E
  set L := Dw.La
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have hspan0 : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hJ0 : J ≠ ⊥ := fun h => hp0 (by rw [h] at hpJ; exact (Submodule.mem_bot R).1 hpJ)
  haveI hfinJ : Finite (R ⧸ J) := (Ideal.absNorm_ne_zero_iff J).1 (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h))
  haveI : Finite (R ⧸ Ideal.span {(p : R)}) :=
    (Ideal.absNorm_ne_zero_iff _).1 (fun h => hspan0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hq : Nat.card (R ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

  haveI hA : Finite (L ⧸ pSub Dw p) := by
    haveI : Finite ((R ⧸ Ideal.span {(p : R)}) ⊗[R] L) := Module.finite_of_finite (R ⧸ Ideal.span {(p : R)})
    exact Finite.of_equiv _ (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(p : R)})).toEquiv
  set V := Submodule.torsionBySet R (L ⧸ pSub Dw p) (J : Set R)

  have hc : ∀ x : L ⧸ pSub Dw p, (p : R) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  obtain ⟨π, hπ⟩ := IsDedekindDomain.exists_sup_span_eq
    (show Ideal.span {(p : R)} ≤ J from (Ideal.span_singleton_le_iff_mem J).2 hpJ) hspan0
  have hle : pSub Dw p ≤ J • (⊤ : Submodule R L) :=
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).2 hpJ)
  have hmap : J • (⊤ : Submodule R (L ⧸ pSub Dw p)) = (J • (⊤ : Submodule R L)).map (pSub Dw p).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hV : Nat.card V = Ideal.absNorm J ^ Module.finrank R L := by
    rw [card_torsion_eq hπ hc, hmap,
      Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ hle).toEquiv,
      ← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L J).toEquiv,
      Module.natCard_eq_pow_finrank (K := R ⧸ J), GlobalTheory.SW.Hyper.finrank_fibre R L (R ⧸ J), hq]
  haveI : Finite V := inferInstance
  haveI : Module.Finite (R ⧸ J) V := Module.Finite.of_finite
  have hq2 : 2 ≤ Ideal.absNorm J := by
    rw [← hq]
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ.ne_top
    exact Finite.one_lt_card
  have hinj := Nat.pow_right_injective hq2
  have hdim : Module.finrank (R ⧸ J) V = Module.finrank R L := by
    apply hinj
    show Ideal.absNorm J ^ _ = Ideal.absNorm J ^ _
    rw [← hV, Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
  rw [Nat.card_congr (latEquiv Dw p J _), card_sub_eq]
  have key : ∀ S : Submodule (R ⧸ J) V, Nat.card S = Ideal.absNorm J ^ k ↔ Module.finrank (R ⧸ J) S = k := by
    intro S
    rw [Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
    exact hinj.eq_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), GlobalTheory.GaussCount.subspaceCount (R ⧸ J) V k, hq, hdim]

end GlobalTheory.LatCountGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctional
section
open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

noncomputable section
open MvPolynomial GlobalTheory.KJInf

namespace GlobalTheory.AvgJet

variable {ι : Type} [Fintype ι]

def evalL {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, smul_eval]

theorem evalL_apply {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : evalL y F = evalAt y F := rfl

theorem dual_eq_sum_evalAt {a : ℕ} (V : Submodule ℂ (PY ι a)) [FiniteDimensional ℂ V]
    (hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) (Λ : Module.Dual ℂ V) :
    ∃ (S : Finset {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}) (c : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ),
      ∀ v : V, Λ v = ∑ y ∈ S, c y * evalAt y.1 (v : PY ι a) := by
  set E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ
    (Set.range fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} => (evalL y.1).comp V.subtype) with hE
  have hco : E.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    rw [Submodule.mem_dualCoannihilator] at hv
    have h0 : (v : PY ι a) = 0 := hsep _ fun y hy => hv _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    exact Subtype.ext h0
  have htop : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hco, Submodule.dualAnnihilator_bot]
  have hΛ : Λ ∈ E := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΛ
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply, smul_eq_mul]

theorem evalAt_rhoK {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (G : VV ℂ lam)
    (Y : ι → Matrix (Fin n) (Fin n) ℂ) :
    evalAt Y ((rhoK lam (invTrK g⁻¹) G : VV ℂ lam) : PY ι n) =
      (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
        evalAt (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Y τ) (G : PY ι n) := by
  have htr : trAct (invTrK g⁻¹) = lft (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold trAct lft Formalism.GradedWeylDivisibility.blockAct
    congr 1
  have hdet : detTwK lam (invTrK g⁻¹) =
      ∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [detPow, invTrK, inside₂, Units.val_zpow_eq_zpow_val]
  show evalAt Y (actP lam (invTrK g⁻¹) G) = _
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, htr, hdet]
  rw [evalAt, smul_eval, ← evalAt, evalAt_lft]

theorem integrable_term {a b : ℕ} {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (Λ : FP ι a b →ₗ[ℂ] ℂ) (Q : FP ι a b) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) ν := by
  set U := GlobalTheory.KJAvg.univSubst Q with hU
  set p : PY ι a := ∑ m ∈ U.support, C (Λ (monomial m 1)) * AddMonoidAlgebra.coeff U m with hp'
  have hp : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, Λ (mvZ g (fun _ => 1) Q) = eval (fun w => g w.1 w.2.1 w.2.2) p := by
    intro g
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff Λ U.support _ (support_map_subset _ _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hp', map_sum, map_mul, eval_C, coeff_map]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) =
      fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F := by
    funext k
    rw [hp]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  rw [e]
  exact GlobalTheory.KJAvg.integrable_avg_term ν hr p y F

end GlobalTheory.AvgJet


open GlobalTheory.AvgJet in
theorem GlobalTheory.AvgJet.avg_jet : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  intro ι _ a b hab ha lam lam' nn hJ K _ _ _ _ _ ν _ _ r hr Q Λ
  classical
  obtain ⟨-, hcomp, -, -, -, -, hsep, -⟩ := _root_.GlobalTheory.KJInf.substIdentities ι a b hab
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨S, c, hΛ⟩ := dual_eq_sum_evalAt (VV ℂ lam) hsep Λ
  have hav := fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} =>
    GlobalTheory.KJAvg.avg_span ι a b hab ha lam nn K ν (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) hr y.1 Q
  choose m y' s hinv hspan using hav
  let d : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ := fun y => (∏ τ, (y.1 τ).det ^ nn τ)⁻¹
  refine ⟨∑ y ∈ S, (c y * d y) • ∑ j, s y j • (evalL (y' y j)).comp (VV ℂ lam').subtype, fun ℓ h v => ?_⟩
  let hh : ι → Matrix (Fin b) (Fin b) ℂ := fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ)
  let Hh : ℂ := ∏ τ, (hh τ).det ^ (lam' τ).detShift
  let ℓ₀ : FP ι a b →ₗ[ℂ] ℂ := ℓ ∘ₗ (mvZ (fun _ => 1) hh).toLinearMap
  let F : PY ι a := (v : PY ι a) * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ nn τ
  have hFV : F ∈ Vn lam nn := ⟨v, (GlobalTheory.KJInf.ClsVal.cSpan_eq_VV' lam).symm ▸ v.2, rfl⟩

  have hpt : ∀ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) =
        Hh * ∑ y ∈ S, c y * d y * (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F) := by
    intro k
    have hsub : GlobalTheory.CompactHowe.substF hh (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q =
        mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) := by
      rw [hcomp]
      simp only [mul_one, one_mul, Matrix.coe_units_inv]
      rfl
    rw [map_inv r k, hΛ]
    simp only [evalAt_rhoK]
    rw [hsub]
    set L := ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) with hL
    have hL' : ℓ (mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q)) = L := rfl
    have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
    rw [hL', Finset.prod_mul_distrib, hH, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdet : ∀ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun τ => (Matrix.isUnits_det_units _).ne_zero
    have key : (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift)) *
        (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) =
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← zpow_add₀ (hdet τ), sub_add_cancel, zpow_natCast]
    have hdy : d y * ∏ τ, (y.1 τ).det ^ nn τ = 1 :=
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (y.2 τ).ne_zero)
    have hF : evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F =
        evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
          ((∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * ∏ τ, (y.1 τ).det ^ nn τ) := by
      rw [GlobalTheory.KJInf.ValPol.evalAt_mul_prod, ← Finset.prod_mul_distrib]
      simp only [Matrix.det_mul, mul_pow]
    rw [hF]
    linear_combination (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a)) * key -
      (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * hdy
  have hint : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}, Integrable (fun k => c y * d y *
      (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F)) ν :=
    fun y => (integrable_term ν hr ℓ₀ Q y.1 F).const_mul _
  have hjet : ((Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v : VV ℂ lam') : PY ι b) =
      Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) := by
    have hx : Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) =
        ((⟨_, hJ _ _ v.2⟩ : VV ℂ lam') : PY ι b) := rfl
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hx, Submodule.projectionOnto_apply_left]
  have hav' : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y},
      ∫ k, ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F ∂ν =
        ∑ j, s y j * ℓ (subY hab (fun τ => hh τ * y' y j τ) F) := by
    intro y
    rw [hspan y F hFV ℓ₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    show s y j * ℓ (mvZ (fun _ => 1) hh (subY hab (y' y j) F)) = _
    rw [mvZ_subY]
  have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, hav']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply,
    smul_eq_mul, evalAt_rhoK, hjet, GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_gen_isoLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  have hL₁ : Z.o₁.t.PP.L.IsLB := Z.o₁.t.PP.isLB
  have hL₂ : Z.o₂.t.PP.L.IsLB := Z.o₂.t.PP.isLB
  obtain ⟨w₁, hw₁, -⟩ := Z.m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := Z.m₂.lin
  have i₁ : LBIso Z.o₁.t.PP.L (Xo.univ.t.PP.L.pull Z.m₁.cm.F) := ⟨w₁, hw₁⟩
  have i₂ : LBIso Z.o₂.t.PP.L (Xo.univ.t.PP.L.pull Z.m₂.cm.F) := ⟨w₂, hw₂⟩
  have i₃ : LBIso (lbPow Z.o₁.t.PP.L (p ^ 2)) (Xo.univ.t.PP.L.pull (Z.ψ.left ≫ Z.m₂.cm.F)) :=
    GlobalTheory.ThetaAffineGlue.lbIso_comp (isLB_lbPow hL₁ _) hL₂ hL Z.isog.1.2.2.2.2.2 i₂
  have i₄ := GlobalTheory.ThetaAffineGlue.lbIso_pull i₃ (hkLift Z h hx)
  have i₅ := GlobalTheory.Spread.lbIso_pow_pull_comp hL hL₁ i₁ (hkLift Z h hx) (hkLift_φ Z hx).symm (p ^ 2)
  have i₆ := lbIso_lbPow_pull hL₁ (hkLift Z h hx) (p ^ 2)
  have i₇ := GlobalTheory.EmbVA.lbIso_pow hL (snd (Over.mk x) Xo.univ.t.G).left (p ^ 2) ((p : ℤ) ^ 2) (by push_cast; rfl)
  have i₈ := ((i₇.trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL _) _)
    (isLB_lbPow (pull_isLB hL₁ _) _) i₅.symm).trans (LB.isLB_linComb hL _ _) (isLB_lbPow (pull_isLB hL₁ _) _)
    (pull_isLB (isLB_lbPow hL₁ _) _) i₆).trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL₁ _) _)
    (pull_isLB hL _) i₄
  have e := (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).1 i₈
  rw [Fin.prod_univ_one, Fintype.prod_unique, zpow_one] at e
  refine (GlobalTheory.PrimNorm.hasGen_iff hL (isoφ Xo.univ.t.G (hkMap Z hx hx')) ![(p : ℤ) ^ 2, -1]).2 ?_
  rw [prod_iso', hkMap_snd, e, mul_inv_cancel]

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_value_sum_weight_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  first | exact @GlobalTheory.HeckeWeight.hkVal_frBor | exact GlobalTheory.HeckeWeight.hkVal_frBor | (intros; apply GlobalTheory.HeckeWeight.hkVal_frBor <;> assumption)
end

