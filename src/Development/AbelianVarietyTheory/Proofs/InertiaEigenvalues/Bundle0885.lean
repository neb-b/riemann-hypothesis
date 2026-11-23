module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIoLFRecIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficients
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescBD

section Abstract

theorem exists_retr_abs {Z O O' K K' : Type} [CommRing Z] [CommRing O] [CommRing O'] [IsDedekindDomain O]
    [Field K] [Field K'] [Algebra O K] [IsFractionRing O K] [Algebra Z O] [Algebra Z O'] [Module.Finite Z O']
    (f : O →+* O') (hf : ∀ c, algebraMap Z O' c = f (algebraMap Z O c)) (j : O' →+* K') (φ : K →+* K')
    (hc : ∀ a, φ (algebraMap O K a) = j (f a)) (hs : ∀ x : K', ∃ a : K, a ≠ 0 ∧ ∃ y, j y = φ a * x) :
    ∃ R : K' →+ K, (∀ a x, R (φ a * x) = a * R x) ∧ (∀ a, R (φ a) = a) ∧ ∀ x, ∃ y, j y = φ (R (j x)) := by
  letI : Algebra K K' := φ.toAlgebra
  letI : Algebra O K' := (φ.comp (algebraMap O K)).toAlgebra
  letI : Algebra O O' := f.toAlgebra
  letI : Algebra O' K' := j.toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq hc
  haveI : IsScalarTower Z O O' := IsScalarTower.of_algebraMap_eq hf
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite Z _ _
  let L : Submodule O K' := LinearMap.range (IsScalarTower.toAlgHom O O' K').toLinearMap
  haveI : Module.Finite O L := inferInstance
  have hsp : Submodule.span K (L : Set K') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, y, hy⟩ := hs x
    have e : x = a⁻¹ • j y := by
      rw [hy]
      change x = φ a⁻¹ * (φ a * x)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.St.G.Inter.exists_retraction (O := O) (K := K)
    (Algebra.linearMap K K') φ.injective L hsp
  exact ⟨T.toAddMonoidHom, fun a x => T.map_smul a x, hT, fun x => hT' (j x) ⟨x, rfl⟩⟩

theorem mem_BD_iff {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) O) (z : Γ → (Fin k → K) ⧸ stdG O K k) :
    z ∈ BD (stdLatG hinj N) ↔ ∃ m : Fin k → K, ∀ g v, Submodule.Quotient.mk v = z g →
      ∃ u : Fin k → O, ∀ j, algebraMap O K (u j) = ∑ t, algebraMap O K (N g j t) * m t - m j - v j := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨m, fun g v hv => ?_⟩
    have hg := (congrFun hm g).trans hv.symm
    have hg' : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := (Submodule.Quotient.eq _).1 hg
    obtain ⟨u, hu⟩ := hg'
    exact ⟨u, fun j => congrFun hu j⟩
  · rintro ⟨m, hm⟩
    refine ⟨Submodule.Quotient.mk m, funext fun g => ?_⟩
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (z g)
    obtain ⟨u, hu⟩ := hm g v hv
    have key : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := ⟨u, funext hu⟩
    exact ((Submodule.Quotient.eq _).2 key).trans hv

theorem desc_abs {O K O' K' : Type} [CommRing O] [Field K] [Algebra O K] [CommRing O'] [Field K'] [Algebra O' K']
    (hinj : Function.Injective (algebraMap O K)) (hinj' : Function.Injective (algebraMap O' K'))
    (f : O →+* O') (φ : K →+* K') (hc : ∀ a, algebraMap O' K' (f a) = φ (algebraMap O K a))
    (R : K' →+ K) (hR : ∀ a x, R (φ a * x) = a * R x) (hR1 : ∀ a, R (φ a) = a)
    (hRO : ∀ x, ∃ y, algebraMap O K y = R (algebraMap O' K' x))
    {Γ : Type} [Group Γ] {k : ℕ} (N : Γ →* Matrix (Fin k) (Fin k) O)
    (q : (Fin k → K) ⧸ stdG O K k → (Fin k → K') ⧸ stdG O' K' k)
    (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => φ (v j)))
    (z : Γ → (Fin k → K) ⧸ stdG O K k) (hz : (fun g => q (z g)) ∈ BD (stdLatG hinj' (mapM f N))) :
    z ∈ BD (stdLatG hinj N) := by
  obtain ⟨m, hm⟩ := (mem_BD_iff hinj' (mapM f N) (fun g => q (z g))).1 hz
  refine (mem_BD_iff hinj N z).2 ⟨fun j => R (m j), fun g v hv => ?_⟩
  obtain ⟨u, hu⟩ := hm g (fun j => φ (v j)) (by rw [← hv, hq])
  choose r hr using hRO
  refine ⟨fun j => r (u j), fun j => ?_⟩
  have hj : algebraMap O' K' (u j) = ∑ t, algebraMap O' K' (f (N g j t)) * m t - m j - φ (v j) := hu j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hr, hj, map_sub, map_sub, map_sum, hR1]
  simp only [hc, hR]

end Abstract

section Gen
variable {l : ℕ} [Fact l.Prime]

theorem exists_retr {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ R : ↥LL'.1 →+ ↥LL.1, (∀ a x, R (IntermediateField.inclusion h a * x) = a * R x) ∧
      (∀ a, R (IntermediateField.inclusion h a) = a) ∧ ∀ x ∈ OL LL', R x ∈ OL LL := by
  haveI := LL.2
  haveI := LL'.2
  haveI : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL'.1 (integralClosure ℤ_[l] ↥LL'.1)
  obtain ⟨R, h1, h2, h3⟩ := exists_retr_abs (Z := ℤ_[l]) (O := ↥(OL LL)) (O' := ↥(OL LL')) (K := ↥LL.1)
    (K' := ↥LL'.1) (incO h) (fun _ => rfl) (OL LL').val.toRingHom (IntermediateField.inclusion h).toRingHom
    (fun _ => rfl) (fun x => by
      have hx : IsAlgebraic ℤ_[l] x :=
        (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL'.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
      refine ⟨algebraMap ℤ_[l] ↥LL.1 y, ?_, ⟨y • x, hi⟩, Algebra.smul_def y x⟩
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      simpa using hy)
  refine ⟨R, h1, h2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h3 ⟨x, hx⟩
  have hy' : (y : ↥LL'.1) = ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x) := hy
  have : IsIntegral ℤ_[l] (((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x)) := hy' ▸ y.2
  exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
    (IntermediateField.inclusion h).injective).1 this

theorem desc {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) ↥(OL LL))
    (z : Γ → (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k)
    (hz : (fun g => liftQ h k (z g)) ∈
      BD (stdLatG (O := ↥(OL LL')) (LL := ↥LL'.1) Subtype.val_injective (mapM (incO h) N))) :
    z ∈ BD (stdLatG (O := ↥(OL LL)) (LL := ↥LL.1) Subtype.val_injective N) := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_retr h
  exact desc_abs (O := ↥(OL LL)) (K := ↥LL.1) (O' := ↥(OL LL')) (K' := ↥LL'.1) Subtype.val_injective
    Subtype.val_injective (incO h) (IntermediateField.inclusion h).toRingHom (fun _ => rfl) R hR hR1
    (fun x => ⟨⟨R x, hRO _ x.2⟩, rfl⟩) N (liftQ h k) (liftQ_mk h k) z hz

end Gen

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) :=
  fun D i w hw C _ M z hz => desc C.le (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w))) z hz

end GlobalTheory.UseLoc.DescBD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphism
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IoConj

section General

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {c : Coeff l} (j : c.F →+* c.F) {n : ℕ}

theorem gaStar_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) (ga : Matrix (Fin n) (Fin n) E)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.L2.Pj.gaStar c ga (map j P) = map j (Formalism.L2.Pj.gaStar c ga P) := by
  induction P using MvPolynomial.induction_on with
  | C x => rw [map_C, Formalism.L2.Pj.gaStar, aeval_C, aeval_C, algebraMap_eq, map_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.L2.Pj.gaStar, aeval_X, letB, map_sum, map_mul, map_C, map_X, hj]

theorem pG_map (a : (E →+* ℂ) × ℕ → ℕ) : map j (pG (Dw := Dw) c a n) = pG (Dw := Dw) c a n := by
  have h : ∀ s i hi col, minorPolynomial (Dw := Dw) (n := n) c s i hi col = map j (minorPolynomial c s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  symm
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero]

theorem rhoM_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (lam : Ix → DomWeight n) (ga : Matrix (Fin n) (Fin n) E) (v v' : VVc c lam)
    (h : (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n)) :
    (rhoM c (fun t => embF c (pl t)) lam ga v' : Pol c.F Ix n) =
      map j (rhoM c (fun t => embF c (pl t)) lam ga v : Pol c.F Ix n) := by
  unfold rhoM
  split_ifs with hg
  · show actP lam _ (v' : Pol c.F Ix n) = map _ (actP lam _ (v : Pol c.F Ix n))
    rw [h]
    refine GlobalTheory.IoExtend.polyAction_map _ lam _ _ (fun t => ?_) _
    refine Matrix.ext fun a b => ?_
    exact (hj (pl t) _).symm
  · simp

theorem exists_stable (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (hpl : Function.Injective pl) (hin : ∀ σ, InPsi H σ ↔ ∃ t, σ = pl t)
    (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam)
    (h : IoLFRec c (fun t => embF c (pl t)) lam a io hw) :
    ∃ N : Submodule c.F (VVc c lam), hw ∈ N ∧
      (∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → ∀ v ∈ N, rhoM c (fun t => embF c (pl t)) lam ga v ∈ N) ∧
      ∀ v ∈ N, ∀ v' : VVc c lam, (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n) → io v' = map j (io v) := by
  obtain ⟨hok, cga, h⟩ := h
  let e : Ix ≃ GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.Psi H := Equiv.ofBijective (fun t => ⟨pl t, (hin _).2 ⟨t, rfl⟩⟩)
    ⟨fun s t hst => hpl (congrArg Subtype.val hst), fun σ => by
      obtain ⟨t, ht⟩ := (hin σ.1).1 σ.2
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  obtain ⟨ha, d, -, hd⟩ := GlobalTheory.LFCompare.pins_of_ioLF Dw c n e a lam io hw cga hok h
  have hcga : ∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → j (cga ga) = cga ga := fun ga hga => by
    rw [hd ga hga, GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.vacChar, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_zpow₀]
    exact congrArg (· ^ _) (hj _ _)
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := h
  let up : VVc c lam → VVc c lam := fun v => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV j lam _ v.2⟩
  refine ⟨
    { carrier := {v | io (up v) = map j (io v)}
      add_mem' := fun {v w} hv hw' => ?_
      zero_mem' := ?_
      smul_mem' := fun s v hv => ?_ }, ?_, fun ga hga v hv => ?_, fun v hv v' hv' => ?_⟩
  · have e1 : up (v + w) = up v + up w := Subtype.ext (map_add (map j) _ _)
    show io (up (v + w)) = _
    rw [e1, map_add (f := _), map_add (f := _), map_add (f := _), show io (up v) = _ from hv, show io (up w) = _ from hw']
  · have e1 : up 0 = 0 := Subtype.ext (map_zero (map j))
    show io (up 0) = _
    rw [e1, map_zero, map_zero]
  · set_option synthInstance.maxHeartbeats 200000 in
    have e1 : up (s • v) = j s • up v := Subtype.ext (GlobalTheory.IoExtend.map_smul' j s _)
    show io (up (s • v)) = _
    rw [e1, map_smul, map_smul, GlobalTheory.IoExtend.map_smul', show io (up v) = _ from hv]
  · have e1 : up hw = hw := by
      apply Subtype.ext
      show map j (hw : Pol c.F Ix n) = _
      rw [show (hw : Pol c.F Ix n) = _ from hok, GlobalTheory.Proof.TensorMapDescent.map_ten]
      simp only [Formalism.L2.DIV.map_extremal]
    show io (up hw) = _
    rw [e1, h7, pG_map]
  · have e1 : up (rhoM c (fun t => embF c (pl t)) lam ga v) = rhoM c (fun t => embF c (pl t)) lam ga (up v) :=
      Subtype.ext (rhoM_map j hj pl lam ga v (up v) rfl).symm
    show io (up _) = _
    rw [e1, h4 ga hga, h4 ga hga, GlobalTheory.IoExtend.map_smul', hcga ga hga, show io (up v) = _ from hv, gaStar_map j hj]
  · rw [show v' = up v from Subtype.ext hv']
    exact hv

theorem eq_top_of_span {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup M] [Module ℂ M]
    {σ : K →+* ℂ} (c0 : X →ₛₗ[σ] M)
    (hli : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ (fun k => c0 (b k)))
    (N : Submodule K X) (hN : Submodule.span ℂ (c0 '' (N : Set X)) = ⊤) : N = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  obtain ⟨B, hB⟩ := GlobalTheory.AdTh.PhaseMap.exists_ext (N := ℂ) c0 hli
    { toFun := fun v => σ (f v)
      map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s v => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
  replace hB : ∀ v, B (c0 v) = σ (f v) := hB
  have h1 : Submodule.span ℂ (c0 '' (N : Set X)) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show B (c0 v) = 0
    rw [hB, show f v = 0 from hf hv, map_zero]
  refine hf0 (LinearMap.ext fun v => ?_)
  have h2 : B (c0 v) = 0 := h1 (hN ▸ Submodule.mem_top)
  rw [hB] at h2
  exact (map_eq_zero σ).1 h2

end General

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


set_option maxHeartbeats 1600000 in
theorem io_map_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) → M.io x' = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hfw i Tp tup O hO τ ta hta hfix x x' hx
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record_ofCore D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
  obtain ⟨n1, n2, -, n4⟩ := GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨-, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hj : ∀ σ y, (ta : O.c'.F →+* O.c'.F) (embF O.c' σ y) = embF O.c' σ y := fun σ y =>
    Subtype.ext ((hta _).trans (hfix.host σ y))
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_stable (ta : O.c'.F →+* O.c'.F) hj (tauE D) (GlobalTheory.SmoothForms.RealPts.tauE_injective D) w1
    (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have htop : N = ⊤ := by
    refine eq_top_of_span O.c0' n4 N ((r2 _ fun γ => ?_).resolve_left fun h0 => ?_)
    · obtain ⟨γE, -, -, h1, -, -, -, h5, -⟩ := GlobalTheory.AdTh.PhaseMap.rat_parts hθ hP.std γ
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨_, hN2 _ h5 v hv, n2 γ γE h1 v⟩
    · have h1 : O.c0' O.hw ∈ Submodule.span ℂ (O.c0' '' (N : Set _)) := Submodule.subset_span ⟨_, hN1, rfl⟩
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, norm_zero] at n1
      exact zero_ne_one n1
  exact hN3 x (htop ▸ Submodule.mem_top) x' hx

end Main

end GlobalTheory.IoConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def intO : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

def Xq (lam : O) (a : ℕ) : Submodule O (LL ⧸ intO (O := O) LL) :=
  LinearMap.ker (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] (LL ⧸ intO (O := O) LL)))

variable {LL}
variable {V V' : Type} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module LL V'] [Module O V']
  [IsScalarTower O LL V']

def scalQ (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') (t : ↥T) :
    (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  (intO (O := O) LL).liftQ (T'.mkQ ∘ₗ (LinearMap.id : LL →ₗ[O] LL).smulRight (j t)) (by
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.linearMap_apply, algebraMap_smul]
    exact T'.smul_mem c (hj t t.2))

def scalB (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T →ₗ[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' where
  toFun := scalQ T T' j hj
  map_add' t u := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_add]
  map_smul' c t := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_comm s c]

def iotaG (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T ⊗[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  TensorProduct.lift (scalB T T' j hj)

theorem iotaG_tmul (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T')
    (t : ↥T) (s : LL) :
    iotaG T T' j hj (t ⊗ₜ Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • j t) := rfl

end Gen

section Conc

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def iotaW (lam : O) (a k : ℕ) :
    ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ stdG O LL k :=
  iotaG (stdG O LL k) (stdG O LL k) LinearMap.id (fun _ h => h) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

def constOne : LL →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => LinearMap.id

theorem constOne_mem : ∀ v ∈ intO (O := O) LL, constOne (O := O) LL v ∈ stdG O LL 1 := by
  rintro _ ⟨c, rfl⟩
  simp only [constOne, stdG]
  refine ⟨fun _ => c, ?_⟩
  ext i
  simp

def iotaC (lam : O) (a : ℕ) :
    ↥(intO (O := O) LL) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin 1 → LL) ⧸ stdG O LL 1 :=
  iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

variable {LL}

def latOne (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) :
    Lattice (O := O) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ)) where
  T := intO LL
  stable g x hx := by
    obtain ⟨c, rfl⟩ := hx
    refine ⟨((ψ g : Oˣ) : O) * c, ?_⟩
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.linearMap_apply, Algebra.smul_def]
  fg := by
    rw [intO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL ((intO (O := O) LL : Set LL)) :=
      Submodule.subset_span ⟨1, map_one (algebraMap O LL)⟩
    simpa using Submodule.smul_mem _ x h1

end Conc

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsModStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  first | exact @GlobalTheory.CycGen.main | exact GlobalTheory.CycGen.main | (intros; apply GlobalTheory.CycGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiser
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLocUnif

theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), ∃ lam : ↥(OL LL), Irreducible lam := by
  intro l _ LL
  obtain ⟨hdvr, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact IsDiscreteValuationRing.exists_irreducible ↥(OL LL)

end GlobalTheory.UseLocUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendUnramEmb
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
end

