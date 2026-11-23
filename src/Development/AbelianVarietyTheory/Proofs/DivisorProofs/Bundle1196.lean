module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.RealPlaceCentraliser

section Gen
open scoped Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [Field k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem nondeg (hJ : IsHermND σ J) (b : Fin n → k ⊗[F] E)
    (hb : ∀ a, Formalism.UG.hform (sigR k σ) (JR k J) a b = 0) : b = 0 := by
  have hv : JR (F := F) k J *ᵥ b = 0 := by
    funext i
    have := hb (Pi.single i 1)
    simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have hdet : IsUnit (JR (F := F) k J).det := by
    have : (JR (F := F) k J).det = inclR (F := F) k J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hJ.2).map _
  calc b = ((JR (F := F) k J)⁻¹ * JR (F := F) k J) *ᵥ b := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem zero_of_hx (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) (z : k ⊗[F] Fld P)
    (hz : ∀ y', hx P k x z y' = 0) : z = 0 := by
  have : φ z = 0 := nondeg hJ _ fun a => by
    obtain ⟨y', rfl⟩ := φ.surjective a
    rw [h]; exact hz y'
  simpa using this

theorem isUnit_of_isIsom [Module.Finite F (Fld P)] (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) : IsUnit x := by
  haveI : Module.Finite k (k ⊗[F] Fld P) := Module.Finite.base_change F k (Fld P)
  have hinj : Function.Injective (LinearMap.mulLeft k x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    refine zero_of_hx hJ h y fun y' => ?_
    simp only [LinearMap.mulLeft_apply] at hy
    simp [hx, hy]
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] E) : sigR k σ (sigR k σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem hform_herm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (a b : Fin n → k ⊗[F] E) :
    sigR k σ (Formalism.UG.hform (sigR k σ) (JR k J) a b) = Formalism.UG.hform (sigR k σ) (JR k J) b a := by
  have hG : ∀ i j, sigR k σ (JR (F := F) k J i j) = JR (F := F) k J j i := by
    intro i j
    simp only [JR, Matrix.map_apply, inclR]
    change sigR k σ (1 ⊗ₜ J i j) = 1 ⊗ₜ J j i
    simp [sigR, hJ.1]
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofBijective σ (Function.Involutive.bijective hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofBijective (star' P) (Algebra.IsAlgebraic.algHom_bijective _)
  have he : (algebraMap E (Fld P)).comp (e₁ : E →+* E) = (e₂ : Fld P →+* Fld P).comp (algebraMap E (Fld P)) :=
    RingHom.ext fun e => (star'_algebraMap P e).symm
  have := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  have h2 := congrArg e₁ this
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.symm

theorem trBase_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] Fld P) :
    trBase P k (sigR k (star' P) z) = sigR k σ (trBase P k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => simp [trBase, sigR, trace_star hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem plusUnits_gen [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ∃ u : plusUnits P k, u.1.1 = x := by
  have hu := isUnit_of_isIsom hJ h
  have hsym : ∀ y, trBase P k ((x - sigR k (star' P) x) * sigR k (star' P) y) = 0 := by
    intro y
    have h1 := h 1 y
    have h2 := h y 1
    have h3 := hform_herm hσ hJ (φ 1) (φ y)
    rw [h2, h1] at h3
    simp only [hx, map_one, mul_one] at h3
    rw [← trBase_star hσ, map_mul] at h3
    rw [sub_mul, map_sub, ← h3, sub_self]
  have hd : x - sigR k (star' P) x = 0 := by
    obtain ⟨v, hv⟩ := hu
    have h0 := zero_of_hx hJ h (↑v⁻¹ * (x - sigR k (star' P) x)) fun y' => by
      simp only [hx]
      rw [show x * (↑v⁻¹ * (x - sigR k (star' P) x)) * sigR k (star' P) y' =
          (x - sigR k (star' P) x) * sigR k (star' P) y' by
        rw [← mul_assoc, ← hv, Units.mul_inv, one_mul]]
      exact hsym y'
    have := congrArg (fun w => (v : k ⊗[F] Fld P) * w) h0
    simpa [← mul_assoc] using this
  refine ⟨⟨hu.unit, ?_⟩, rfl⟩
  show Units.map (sigR k (star' P)).toMonoidHom hu.unit = MonoidHom.id _ hu.unit
  ext
  simpa using (sub_eq_zero.mp hd).symm

end Gen

theorem plusUnits_of_isIsom {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) :
    ∃ u : plusUnits P (placeOf D ρ).Completion, u.1.1 = x := by
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  exact plusUnits_gen (fun e => star_star e) (GlobalTheory.DefiniteQuotient.gram_hermND V) h

theorem topGrp {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borel {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

theorem torComm {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (s t : HA R σ J) : s * t = t * s := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  change (s.1.1 * t.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0 = (t.1.1 * s.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0
  simp [Matrix.mul_apply, mul_comm]

theorem measFacts {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : G, a * b = b * a) (e : G ≃ₜ* H) (dt : Measure G) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant ∧ (dt.map e).real univ = dt.real univ ∧
      (CompactSpace H ↔ CompactSpace G) := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have := congrArg e (hc (e.symm a) (e.symm b))
    simpa [map_mul] using this
  haveI hH : (dt.map e).IsHaarMeasure := e.isHaarMeasure_map dt
  refine ⟨hH, ⟨fun g => ?_⟩, ?_, ?_⟩
  · have : (fun a : H => a * g) = (fun a => g * a) := funext fun a => hcomm a g
    rw [this]
    exact map_mul_left_eq_self _ g
  · rw [Measure.real, Measure.real, Measure.map_apply (show Measurable (e : G → H) from e.continuous.measurable) MeasurableSet.univ, Set.preimage_univ]
  · exact ⟨fun hc => e.toHomeomorph.symm.compactSpace, fun hc => e.toHomeomorph.compactSpace⟩

theorem centMeas_real_place : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  intro D V P ρ dt _ x φ h
  obtain ⟨u, rfl⟩ := plusUnits_of_isIsom V P ρ h
  have H := _root_.GlobalTheory.TorCentTop.torEquiv_cent D.host.F D.host.E D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.rank P V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) (placeOf D ρ).Completion u φ h
  obtain ⟨e, H2⟩ := H
  have hm := H2.2
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  haveI := topGrp (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := topGrp (placeOf D ρ).Completion (star' P) (one₁ P)
  haveI := borel (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := borel (placeOf D ρ).Completion (star' P) (one₁ P)

  simp only [hm dt]
  have hc := torComm (placeOf D ρ).Completion (star' P) (one₁ P)
  have hf := measFacts (G := Tor P (placeOf D ρ).Completion) (H := cent (gam h)) hc e dt
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  rw [isCompact_iff_compactSpace]
  exact hf.2.2.2

end GlobalTheory.RealPlaceCentraliser
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.HCAlpha

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem vecF_eqOn_invSet (X : Lie E a) {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (vecF E a X f) (vecF E a X f') (invSet E a) := fun y hy => by
  have e : f =ᶠ[nhds y] f' := Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) h
  simp only [vecF, e.fderiv_eq]

theorem lapF_eqOn_invSet {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (lapF E a f) (lapF E a f') (invSet E a) := fun y hy => by
  simp only [lapF, Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy, vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy]

theorem chart_lie_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lie E a X φ).1 g) (vecF E a X (chart φ.1 g)) (invSet E a) := fun _ hy =>
  chart_lieD φ.2 X g hy

theorem chart_lie_sq_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart ((lie E a X ^ 2) φ).1 g) (vecF E a X (vecF E a X (chart φ.1 g))) (invSet E a) := by
  rw [sq]
  exact (chart_lie_eqOn_invSet X (lie E a X φ) g).trans (vecF_eqOn_invSet X (chart_lie_eqOn_invSet X φ g))

theorem chart_lapOp_eqOn_invSet (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lapOp E a φ).1 g) (lapF E a (chart φ.1 g)) (invSet E a) := fun y hy => by
  have hy' : IsUnit (Matrix.of y) := hy
  have key : ∀ X : Lie E a, ((lie E a X ^ 2) φ).1 (g * infGL E a hy'.unit) =
      vecF E a X (vecF E a X (chart φ.1 g)) y := fun X => by
    rw [← chart_lie_sq_eqOn_invSet X φ g hy, chart, dite_eq_left hy']
  rw [chart, dite_eq_left hy']
  simp only [lapOp, lapF, LinearMap.sum_apply, LinearMap.add_apply, Submodule.coe_sum, Submodule.coe_add,
    Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← key, ← key]
  rfl

theorem chart_lapOp_pow (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (g : GA E a) (n : ℕ) :
    ∀ y ∈ invSet E a, chart ((lapOp E a ^ n) φ).1 g y = (lapF E a)^[n] (chart φ.1 g) y := by
  induction n with
  | zero => intro y _; rfl
  | succ n ih =>
    intro y hy
    rw [pow_succ', Function.iterate_succ_apply', Module.End.mul_apply, chart_lapOp_eqOn_invSet _ g hy]
    exact lapF_eqOn_invSet ih hy

end GlobalTheory.HCAlpha

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.Vert.DivPull

section Sections

variable {X Y Y' W : Scheme.{0}}

theorem pullbackComp_inv_app (b : W ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : W.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).inv.app E).app T (pullbackSections (b ≫ a) E h s) =
      pullbackSections b _ h₂ (pullbackSections a E h₁ s) := by
  have e := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)) (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at e
  refine (app_resM _ h _).trans (Eq.trans ?_ (pullbackSections_res b _ h₂ h₁ _).symm)
  exact congrArg (resM _ h) congr(($e).app U s).symm

theorem detUnit_congr {F : X.Modules} {r : ℕ} {U U' T T' V : X.Opens} {e : Fin r → Γ(F, U)}
    {e' : Fin r → Γ(F, U')} {d : Fin r → Γ(F, T)} {d' : Fin r → Γ(F, T')} (he : IsFrame e)
    (he' : IsFrame e') (hd : IsFrame d) (hd' : IsFrame d') (h : V ≤ U) (h' : V ≤ U') (k : V ≤ T)
    (k' : V ≤ T') (H : ∀ i, resM F h (e i) = resM F k (d i))
    (H' : ∀ i, resM F h' (e' i) = resM F k' (d' i)) :
    he.detUnit he' h h' = hd.detUnit hd' k k' := by
  have e₁ : he.basis h = hd.basis k :=
    DFunLike.ext _ _ fun i => by simp only [IsFrame.basis_apply, H]
  refine Units.ext ?_
  simp only [IsFrame.val_detUnit, e₁, H']

end Sections

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z Z₁ : Model O}
  {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules} {r : ℕ}

end GlobalTheory.Vert.DivPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactWeyl
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
open GlobalTheory.TrEll

noncomputable section
namespace GlobalTheory.RealSigns

def weylSub {n : ℕ} (ε : Fin n → Bool) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ε ∘ ⇑w = ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    ext i; simp

theorem mem_weylSub {n : ℕ} (ε : Fin n → Bool) (w : Equiv.Perm (Fin n)) :
    w ∈ weylSub ε ↔ w ∈ GlobalTheory.HCChar.compactWeyl ε := by
  simp [weylSub, GlobalTheory.HCChar.compactWeyl]

theorem of_cosets (hR : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i)) : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  intro D V S M ρ P hc
  have hR' := hR D V S M P ρ hc (weylSub (M.ε ρ)) (mem_weylSub (M.ε ρ))
  obtain ⟨T, b, hbij, hconj⟩ := hR'
  have hfin : (XSet P (placeOf D ρ).Completion V.gram).Finite :=
    Set.finite_coe_iff.1 (Finite.of_equiv _ b.symm)
  have h1 := @_root_.GlobalTheory.TrEll.realTorus_split D.host.F D.host.E _ _ _ _ _ D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank P
    (placeOf D ρ) (embOverOf D ρ)
  have hnorm : ∀ i, ‖cxRoots (embOverOf D ρ).1 P i‖ = 1 := by
    obtain ⟨Ψ, h3⟩ := h1 (by convert hc using 0)
    exact h3.2.2.2.2.2
  have hexp : ∀ z : ℂ, ‖z‖ = 1 → Complex.exp (Complex.arg z * Complex.I) = z := fun z hz => by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rwa [hz, Complex.ofReal_one, one_mul] at h
  refine ⟨hfin, fun q => (b q : Equiv.Perm (Fin V.rank)),
    fun q a => Complex.arg (cxRoots (embOverOf D ρ).1 P (((b q : Equiv.Perm (Fin V.rank)))⁻¹ a)), ?_,
    fun q a => hexp _ (hnorm _), ?_⟩
  · let e : GlobalTheory.HCChar.compactWeyl (M.ε ρ) ≃ weylSub (M.ε ρ) :=
      { toFun := fun w => ⟨w.1, (mem_weylSub _ _).2 w.2⟩, invFun := fun w => ⟨w.1, (mem_weylSub _ _).1 w.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact hbij.comp (Equiv.prodCongr e b).bijective
  · intro q
    have hq : HasCls P (placeOf D ρ).Completion V.gram (gam q.2.choose_spec.choose_spec.2) q.1 :=
      ⟨_, _, q.2.choose_spec.choose_spec.2, q.2.choose_spec.choose_spec.1, rfl⟩
    have hc2 := hconj q (gam q.2.choose_spec.choose_spec.2) hq
    obtain ⟨g, hg⟩ := hc2
    refine ⟨g⁻¹, (congrArg (fun h => frameMat M ρ (h * gam q.2.choose_spec.choose_spec.2 * g⁻¹)) (inv_inv g)).trans (hg.trans ?_)⟩
    exact congrArg Matrix.diagonal (funext fun a => (hexp _ (hnorm _)).symm)

end GlobalTheory.RealSigns
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountKernelNonzero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem count_kernel_nonzero : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k c M l : ℕ) (ρ : Fin c → (κ →ₐ[ℂ] κ'))
    (w : Fin l → κ), (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → c * (M + k - 1).choose k < l →
  ∃ b : Fin l → κ', b ≠ 0 ∧ ∀ i, ∑ j, w j ⊗ₜ[ℂ] b j ∈
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M := by
  intro κ κ' _ _ _ _ k c M l ρ w hz hlt
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  set J : Fin c → Ideal (κ ⊗[ℂ] κ') := fun i =>
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M with hJ
  have hjet := fun i => GlobalTheory.T.finrank_graphJets_le_choose k M (ρ i) hz
  haveI : ∀ i, Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ J i) := fun i => (hjet i).2
  let g : (Fin l → κ') →ₗ[κ'] (κ ⊗[ℂ] κ') := Fintype.linearCombination κ' (fun j => w j ⊗ₜ[ℂ] (1 : κ'))
  have hg : ∀ b, g b = ∑ j, w j ⊗ₜ[ℂ] b j := by
    intro b
    simp only [g, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    show (1 ⊗ₜ[ℂ] b j) * (w j ⊗ₜ[ℂ] (1 : κ')) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f : (Fin l → κ') →ₗ[κ'] ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ κ' (J i)).toLinearMap.comp g
  have hdim : Module.finrank κ' ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) < Module.finrank κ' (Fin l → κ') := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    calc ∑ i, Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J i) ≤ ∑ _i : Fin c, (M + k - 1).choose k :=
          Finset.sum_le_sum fun i _ => (hjet i).1
      _ = c * (M + k - 1).choose k := by simp
      _ < l := hlt
  obtain ⟨b, hbker, hb0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  refine ⟨b, hb0, fun i => ?_⟩
  have := congr_fun (LinearMap.mem_ker.mp hbker) i
  simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.zero_apply] at this
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hg] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

namespace GlobalTheory.LieVB

theorem bijective_add_mul_epsFn : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  intro O _ V hV
  have H : IsPullback (spMap (algebraMap O (DualNumber O))) (𝟙 _) (𝟙 _)
      (spMap (algebraMap O (DualNumber O))) := IsPullback.of_vert_isIso ⟨by simp⟩
  have h := GlobalTheory.EpsThick.comb_bijective_of_isAffineOpen H hV
  refine Eq.mpr (congrArg Function.Bijective (funext fun ab => ?_)) h
  rw [Scheme.Hom.appLE_eq_app, _root_.mul_comm]
  rfl

end GlobalTheory.LieVB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)) (K'' : Subgroup (GLw n w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ IsOpen (K'' : Set (GLw n w)) ∧ K'' ≤ K'.map (UL n w).subtype ∧ (K''.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).Normal ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, blk (Nat.add_sub_cancel' ha) w (m₁, m₂) 0 ∈ K'') ∧ (∀ m₁ ∈ K₁, ∀ m₂ ∈ K₂, μ (GeneralLinearGroup.det m₁ ^ (n - a) * GeneralLinearGroup.det m₂ ^ a) = 1) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  first | exact @GlobalTheory.BCT.SplitLevels.levels_split | exact GlobalTheory.BCT.SplitLevels.levels_split | (intros; apply GlobalTheory.BCT.SplitLevels.levels_split <;> assumption)
end

