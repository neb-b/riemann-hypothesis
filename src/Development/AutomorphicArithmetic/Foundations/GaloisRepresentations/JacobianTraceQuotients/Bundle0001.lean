module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.LocGal
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open PositivityTheory.Rg.Tf.Geo
open scoped Classical NNReal ENNReal Pointwise

section Local

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k']
  [IsModuleTopology k k']

private theorem cont_norm : Continuous (Algebra.norm k : k' → k) := by
  let b := Module.finBasis k k'
  have e : (Algebra.norm k : k' → k) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [e]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have hl : Continuous ((b.coord i).comp (LinearMap.mulRight k (b j))) :=
    IsModuleTopology.continuous_of_linearMap _
  refine hl.congr fun x => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul]

private theorem nabs_norm [CharZero k] (x : k'ˣ) :
    GlobalTheory.SplitWeil.nabs k (Units.map (Algebra.norm k : k' →* k) x) = GlobalTheory.SplitWeil.nabs k' x := by
  borelize k'
  unfold GlobalTheory.SplitWeil.nabs
  congr 1
  symm
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : k')
  let μ : Measure k' := Measure.addHaar
  have h0 : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨0, mem_interior_iff_mem_nhds.mpr hK0⟩).ne'
  have hf : μ K ≠ ∞ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hf ?_
  let T : k' ≃ₗ[k] k' := DistribMulAction.toLinearEquiv k k' x⁻¹
  have hT := _root_.GlobalTheory.KSp.map_linearEquiv_haar k k' μ T
  have hdet : LinearEquiv.det T = (Units.map (Algebra.norm k : k' →* k) x)⁻¹ := by
    ext
    simp only [LinearEquiv.coe_det, T, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_apply,
      Units.val_inv_eq_inv_val, map_inv₀]
    have hl : (↑(DistribMulAction.toLinearEquiv k k' x⁻¹) : k' →ₗ[k] k') =
        LinearMap.mul k k' ↑x⁻¹ := by
      ext y
      simp [Units.smul_def]
    rw [hl]
    apply eq_inv_of_mul_eq_one_left
    rw [← LinearMap.det_comp]
    have hc : (LinearMap.mul k k' ↑x⁻¹).comp (Algebra.lmul k k' ↑x) = LinearMap.id := by
      ext y
      simp
    rw [hc, LinearMap.det_id]
  have hm : MeasurableSet K := hK.isClosed.measurableSet
  have hTc : Continuous T := IsModuleTopology.continuous_of_linearMap (T : k' →ₗ[k] k')
  have e : Measure.map T μ K = (((distribHaarChar k) (LinearEquiv.det T))⁻¹ • μ) K := by
    rw [hT]
  rw [Measure.map_apply hTc.measurable hm, hdet, map_inv, inv_inv] at e
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  rw [← e]
  congr 1
  ext y
  simp [T, Set.mem_smul_set_iff_inv_smul_mem]

private theorem prod_aut [IsGalois k k'] {M : Type*} [CommMonoid M] (s : k' ≃ₐ[k] k') (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    (f : (k' ≃ₐ[k] k') → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank k k'), f (s ^ i) := by
  have ho : orderOf s = Module.finrank k k' :=
    (orderOf_eq_card_of_forall_mem_zpowers hs).trans (IsGalois.card_aut_eq_finrank k k')
  calc ∏ τ, f τ = ∏ τ ∈ (Finset.range (orderOf s)).image (fun i => s ^ i), f τ := by
        rw [IsCyclic.image_range_orderOf hs]
    _ = ∏ i ∈ Finset.range (orderOf s), f (s ^ i) :=
        Finset.prod_image (fun i hi j hj h =>
          pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) h)
    _ = _ := by rw [ho]

private theorem iter_aut (s : k' ≃ₐ[k] k') (i : ℕ) (x : k') :
    (⇑(s : k' ≃+* k'))^[i] x = (s ^ i) x := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]
    rfl

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  subst h
  have ev : ∀ (u : HeightOneSpectrum (𝓞 E)) (x : E),
      Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
    fun u x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have key : ∀ x : E, Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    rw [galEquiv_algebraMap, ev, ev]
    exact valuation_smul σ w x
  by_cases hy : y = 0
  · simp [hy]
  have hy' : galEquiv v σ w (σ • w) rfl y ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy)
  have h2 := (continuous_galEquiv v σ w (σ • w) rfl).continuousAt.preimage_mem_nhds
    (Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy'))
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap E w).inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : Valued.v (algebraMap E (w.adicCompletion E) x) = Valued.v y := hx.1
  have e2 : Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (galEquiv v σ w (σ • w) rfl y) := hx.2
  rw [← e2, key, e1]

private theorem galFin_eq (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hfix : w.1 = σ • w.1)
    (y : CompletionsOver E v) : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [galFin, galOf, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgEquiv.symm_apply_apply]
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul]
    simp only [Pi.mul_apply, map_mul, Pi.algebraMap_apply, AlgHom.id_apply, AlgEquiv.commutes,
      galEquiv_algebraMap]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _), Pi.add_apply] at ha hb ⊢
    rw [ha, hb]

end Global

open scoped Valued in
theorem UpperTheory.Gal.Join.locGal :
    UpperTheory.Gal.Join.LocGal := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hns
  obtain ⟨-, -, -, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  have hw : ∀ u : PlacesOver E v, u = w := huniq v hns w
  obtain ⟨A, hval, hfin, hgal, s, hs, hrk, hinc, hgf, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  have hA : A = algebraCompletion v w.1 := Algebra.algebra_ext _ _ fun x => (hinc x).symm
  subst hA
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have hse : ∀ z, s z = galEquiv v σ w.1 w.1 hfix z := fun z => by
    have h1 := hgf (Pi.single w z)
    rw [galFin_eq σ w hfix, Pi.single_eq_same] at h1
    exact h1.symm
  have hvs : ∀ z, Valued.v (s z) = Valued.v z := fun z => by
    rw [hse]
    exact val_gal v σ w.1 w.1 hfix z
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : IsModuleTopology (v.adicCompletion F) (w.1.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  refine ⟨(s : _ ≃+* _), Units.map (Algebra.norm (v.adicCompletion F) : w.1.adicCompletion E →* _), fun n g => ?_,
    ⟨⟨fun x => ?_, ?_, fun x => ?_⟩, fun x => ?_, ?_, fun x => ?_⟩, fun x => rfl⟩
  · exact Units.ext (Matrix.ext fun a b => hgf _)
  · exact le_antisymm ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).le)
      ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).ge)
  · exact hp.pos
  · rw [iter_aut, ← hrk, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  · change algebraMap _ _ (Algebra.norm (v.adicCompletion F) (x : w.1.adicCompletion E)) = _
    rw [Algebra.norm_eq_prod_automorphisms, prod_aut s hs, hrk]
    exact Finset.prod_congr rfl fun i _ => (iter_aut s i _).symm
  · exact Continuous.units_map _ cont_norm
  · exact nabs_norm x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD
open scoped Classical

namespace UpperTheory.Gal.Join

def ForRep (p : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (_ : Representation ℂ (GL (Fin n) k) V), Prop) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), p k n V π

structure IsAvg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G)
    (e : V →ₗ[ℂ] V) : Prop where
  mem : ∀ v, e v ∈ fixed π K
  fix : ∀ v ∈ fixed π K, e v = v
  inv : ∀ g ∈ K, ∀ v, e (π g v) = e v
  lin : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (p : V →ₗ[ℂ] W) (v : V), (∀ g ∈ K, p (π g v) = p v) → p (e v) = p v

def AvgEx : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ K : Subgroup G, CO K → ∃ e, IsAvg π K e ∧ ∀ (s : G →* G) (A : V →ₗ[ℂ] V), (∀ g v, A (π g v) = π (s g) (A v)) →
      (∀ g ∈ K, s g ∈ K) → (∀ g ∈ K, ∃ h ∈ K, s h = g) → ∀ v, A (e v) = e (A v)

def DcosOp : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ K : Subgroup G, CO K → ∀ e, IsAvg π K e → ∀ x : G,
      IsIntegralOp μ π ({g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b}.indicator fun _ => 1)
        ((μ.real {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} : ℂ) • (e ∘ₗ π x ∘ₗ e))

def HeckeMul : Prop := ForRep fun k _ _ _ _ n _ _ _ π => ∀ K, IwLev K → ∀ e, IsAvg π K e → ∀ t, Dom t → ∀ v ∈ fixed π K,
  (∀ s, Dom s → e (π (diagT k (Fin n) s) (e (π (diagT k (Fin n) t) v))) = e (π (diagT k (Fin n) (s * t)) v)) ∧
    (twKer π (unipB k (Fin n)) 1).mkQ (e (π (diagT k (Fin n) t) v)) = jacBU π t ((twKer π (unipB k (Fin n)) 1).mkQ v)

def KerKill : Prop := ForRep fun k _ _ _ _ n _ _ _ π => ∀ K, IwLev K → ∀ e, IsAvg π K e →
  ∀ v ∈ twKer π (unipB k (Fin n)) 1, ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
    (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) → e (π (diagT k (Fin n) t) v) = 0

def TraceQuot : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (B : V →ₗ[ℂ] V) (p : V →ₗ[ℂ] W) (T : W →ₗ[ℂ] W), (∀ v, B v ∈ S) → (∀ v ∈ S, p (B v) = T (p v)) →
    (∀ v ∈ S, p v = 0 → ∃ m : ℕ, (B ^ m) v = 0) → HasFinTrace B (trIn (S.map p) T)

def ImStab : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsAdmissible π → ∀ K, IwLev K → FiniteDimensional ℂ (imK π K) ∧
  (∀ t, ∀ y ∈ imK π K, jacB π t y ∈ imK π K) ∧ ∀ (σ : k ≃+* k) A (hA : Semi σ π A), (∀ g, Loc.sg (n := n) σ g ∈ K ↔ g ∈ K) →
    ∀ y ∈ imK π K, jacA hA y ∈ imK π K

def DcosVol : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure]
    (K : Subgroup (GL (Fin n) k)), IwLev K → ∀ t, Dom t →
      Test (el K t) ∧ μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹

def JacNorm : Prop := ForRep fun _ _ _ _ _ _ _ _ _ π => ∀ t y, jacBU π t y = ((Real.sqrt (deltaB t) : ℝ) : ℂ) • jacB π t y

def CasTrace : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsAdmissible π →
  ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure],
    ∀ K, IwLev K → ∀ (σ : k ≃+* k) A (hA : Semi σ π A), Isom σ → (∀ g, Loc.sg (n := n) σ g ∈ K ↔ g ∈ K) → ∀ t, Strict t →
      ∃ B, IsIntegralOp μ π (el K t) B ∧ HasFinTrace (B ∘ₗ A) ((μ.real (K : Set (GL (Fin n) k)) : ℂ) *
        ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹ * trIn (imK π K) (jacB π t ∘ₗ jacA hA))

def NormDom : Prop :=
  ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (ι : k →+* k') (σ : k' ≃+* k') (l : ℕ)
    (N : k'ˣ →* kˣ), IsNorm ι σ l N → (∀ x, N (Units.map (σ : k' →* k') x) = N x) ∧ ∀ (n : ℕ) (t : Fin n → k'ˣ),
      (Strict t → Strict (nT n N t)) ∧ deltaB (nT n N t) = deltaB t ∧ ∀ s, Strict t → Dom s → Strict (t * s)

def CharDom : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t₀ : Fin n → kˣ)
    (E E' : Multiset ((Fin n → kˣ) →* ℂˣ)) (c c' : ℂ), c ≠ 0 →
    (∀ t, Dom t → c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) →
    (∀ μ ∈ E, μ ∈ E') ∧ (E ≠ 0 → ∃ t, Dom t ∧ (E.map fun μ => (μ (t₀ * t) : ℂ)).sum ≠ 0)

def TraceExp : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ T X) (P : Submodule ℂ X)
    [FiniteDimensional ℂ P], (∀ t, ∀ y ∈ P, ρ t y ∈ P) → ∃ E : Multiset (T →* ℂˣ),
      (∀ t, trIn P (ρ t) = (E.map fun μ => (μ t : ℂ)).sum) ∧ ∀ μ, μ ∈ E ↔ ∃ y ∈ P, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y

def TwExp : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ T X) (P : Submodule ℂ X)
    [FiniteDimensional ℂ P] (s : T ≃* T) (A : X →ₗ[ℂ] X), (∀ t, ∀ y ∈ P, ρ t y ∈ P) → (∀ y ∈ P, A y ∈ P) →
    (∀ t y, A (ρ t y) = ρ (s t) (A y)) → ∀ t₁, trIn P (ρ t₁ ∘ₗ A) ≠ 0 →
      ∃ μ : T →* ℂˣ, (∀ t, μ (s t) = μ t) ∧ ∃ y ∈ P, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y

def SubQuot : Prop :=
  ∀ (T X : Type) [CommGroup T] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (ρ : Representation ℂ T X) (μ : T →* ℂˣ),
    ((∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y) ↔ (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥) ∧
    ((∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y) → ∃ l : X →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ t y, l (ρ t y) = (μ t : ℂ) * l y)

def QuotEmb : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → π.IsIrreducible →
  ∀ (ω : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 →
    (∀ t y, l (jacB π t y) = (torusChar ω t : ℂ) * l y) → IsSubquotient π (prinSeries ω)

def ExpSub : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → π.IsIrreducible → ∀ μ, IsExp π μ →
  ∃ ω : Fin n → kˣ →* ℂˣ, μ = torusChar ω ∧ (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient π (prinSeries ω)

def SubPerm : Prop := ForRep fun k _ _ _ _ n _ _ _ π => π.IsIrreducible → ∀ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
  ∀ w : Equiv.Perm (Fin n), IsSubquotient π (prinSeries ω) → IsSubquotient π (prinSeries (ω ∘ w))

def ExpLev : Prop := ForRep fun k _ _ _ _ n _ _ _ π => IsSmooth π → ∀ y : Jacquet π (unipB k (Fin n)),
  ∃ U : Subgroup (GL (Fin n) k), IsOpen (U : Set (GL (Fin n) k)) ∧ ∀ K ≤ U, y ∈ imK π K

end UpperTheory.Gal.Join
end
end

