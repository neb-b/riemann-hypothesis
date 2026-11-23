module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTop
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem covol_le_of_mul_left (Γ Γ' : Set (MatInf E j)) (h : MatInf E j) (hh : 0 < detNorm E j h)
    (A B : Set (MatInf E j)) (hAB : ∀ x ∈ A, h * x ∈ B)
    (hΓ : ∀ δ ∈ Γ', ∃ δ₀ ∈ Γ, ∀ x, h * (δ₀ * x) = δ * (h * x)) :
    covol Γ (haarGL E j) A ≤ covol Γ' (haarGL E j) B := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hmeas : Measurable (fun g : MatInf E j => h * g) :=
    (GlobalTheory.MeanDual.measurePreserving_mul_left E j h hh).measurable
  refine iInf_le_of_le ((fun g => h * g) ⁻¹' D') (iInf_le_of_le (hmeas hD') (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨δ, hδ, hx'⟩ := hc (h * x) (hAB x hx)
    obtain ⟨δ₀, hδ₀, H⟩ := hΓ δ hδ
    refine ⟨δ₀, hδ₀, ?_⟩
    show h * (δ₀ * x) ∈ D'
    rw [H]; exact hx'
  · rw [← Measure.map_apply hmeas hD', GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq E j h hh]

def scal (r : ℝ) : MatInf E j := fun _ a b => if a = b then (r : ℂ) else 0

theorem of_scal (r : ℝ) (w : InfinitePlace E) :
    Matrix.of (scal E j r w) = (r : ℂ) • (1 : Matrix (Fin j) (Fin j) ℂ) := by
  ext a b
  simp [scal, Matrix.one_apply]

theorem scal_mul_comm (r : ℝ) (δ x : MatInf E j) : scal E j r * (δ * x) = δ * (scal E j r * x) := by
  apply matInf_ext
  intro w
  simp only [of_mul, of_scal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

theorem detNorm_scal (r : ℝ) (hr : 0 < r) :
    detNorm E j (scal E j r) = (r ^ (2 * j)) ^ Fintype.card (InfinitePlace E) := by
  unfold detNorm
  simp only [of_scal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, ← pow_mul, mul_comm]

theorem exists_scal (hj : 1 ≤ j) (c : ℝ) (hc : 0 < c) : ∃ r : ℝ, 0 < r ∧ detNorm E j (scal E j r) = c := by
  have hN : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  refine ⟨c ^ (((2 * j * Fintype.card (InfinitePlace E) : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [detNorm_scal E j _ (Real.rpow_pos_of_pos hc _), ← pow_mul]
  exact Real.rpow_inv_natCast_pow hc.le (by positivity)

def slab (c : ℝ) : Set (MatInf E j) := {x | c ≤ detNorm E j x ∧ detNorm E j x < c * Real.exp 1}

theorem covol_slab_le (hj : 1 ≤ j) (Λ : Submodule (𝓞 E) (Fin j → E)) (c : ℝ) (hc : 0 < c) :
    covol (autGL E j Λ) (haarGL E j) (slab E j c) ≤
      covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} := by
  obtain ⟨r, hr, hd⟩ := exists_scal E j hj c⁻¹ (inv_pos.2 hc)
  refine covol_le_of_mul_left E j _ _ (scal E j r) (hd ▸ inv_pos.2 hc) _ _ ?_
    (fun δ hδ => ⟨δ, hδ, fun x => scal_mul_comm E j r δ x⟩)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq, detNorm_mul, hd]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact h1
  · rw [inv_mul_eq_div, div_lt_iff₀ hc, mul_comm]; exact h2

theorem covol_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ≤
      covol (autGL E j Λ') (haarGL E j) (slab E j (detNorm E j (embInf E j γ))) := by
  refine covol_le_of_mul_left E j _ _ (embInf E j γ) (detNorm_embInf E j γ) _ _ ?_ ?_
  · rintro x ⟨h1, h2⟩
    simp only [slab, Set.mem_setOf_eq, detNorm_mul]
    have hp := detNorm_embInf E j γ
    exact ⟨le_mul_of_one_le_right hp.le h1, mul_lt_mul_of_pos_left h2 hp⟩
  · intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
    refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x => ?_⟩
    apply matInf_ext
    intro w
    simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
    have := embInf_inv_mul E j γ⁻¹ w
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]

theorem glVol_lt_top (hE : IsTotallyComplex E) : ∀ j : ℕ, 1 ≤ j → glVol E j < ⊤ := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.NormOneVol.glVol_one E hE]; exact ENNReal.ofReal_lt_top
    · have h := ih hn
      have hs := GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (n + 1) (by omega) (by simpa using h)
      rw [hs]
      simp only [Nat.add_sub_cancel] at h ⊢
      exact ENNReal.mul_lt_top h ENNReal.ofReal_lt_top

end GlobalTheory.SlabFinVol


open GlobalTheory.FlagMeas GlobalTheory.MeanDual in
theorem GlobalTheory.SlabFinVol.covol_unitSlab_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  have hfin := GlobalTheory.SlabFinVol.glVol_lt_top E hE j hj
  let R : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} → Prop :=
    fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1
  have hle : _ ≤ glVol E j := ENNReal.le_tsum (Quot.mk R ⟨Λ, hΛ⟩)
  have hrel := Quot.eqvGen_exact (Quot.out_eq (Quot.mk R ⟨Λ, hΛ⟩))
  have key : ∀ a b, Relation.EqvGen R a b →
      ∃ γ : GL (Fin j) E, Carries E j γ a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel x y h => exact h
    | refl x => exact ⟨1, fun y => by simp⟩
    | symm x y _ ih => obtain ⟨γ, h⟩ := ih; exact ⟨γ⁻¹, h.inv⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨γ, h⟩ := ih1; obtain ⟨δ, h'⟩ := ih2; exact ⟨δ * γ, h'.mul h⟩
  obtain ⟨γ, hγ⟩ := key _ _ hrel
  exact lt_of_le_of_lt ((covol_le_of_carries E j hγ.inv).trans
    (GlobalTheory.SlabFinVol.covol_slab_le E j hj _ _ (detNorm_embInf E j _))) (lt_of_le_of_lt hle hfin)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.InfDecomp

theorem list_prod_map_mulSingle {ι M : Type} [DecidableEq ι] [Monoid M] (w : ι) (a : M) :
    ∀ l : List ι, l.Nodup → (l.map (Pi.mulSingle w a : ι → M)).prod = if w ∈ l then a else 1
  | [], _ => by simp
  | i :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle w a l h.2]
    by_cases hi : i = w
    · subst hi
      simp [h.1]
    · simp [Pi.mulSingle_apply, hi, Ne.symm hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cutPt (v : InfinitePlace E) (x : UA E n) : UA E n := ((embRet (n := n) v.embedding x : embU n v.embedding) : UA E n)

theorem cutPt_mem (v : InfinitePlace E) (x : UA E n) : cutPt v x ∈ embU n v.embedding := (embRet v.embedding x).2

theorem cInf_cutPt (v : InfinitePlace E) (x : UA E n) : cInf (cutPt v x) = cutGL v (cInf x) := by
  unfold cutPt
  rw [cInf_embRet, InfinitePlace.mk_embedding]


open Classical in
theorem evGL_cInf_cutPt (x : UA E n) (v w : InfinitePlace E) :
    evGL w (cInf (cutPt v x)) = (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) v := by
  rw [cInf_cutPt, Pi.mulSingle_apply]
  split_ifs with h
  · subst h
    exact evGL_cutGL_self _ _
  · exact evGL_cutGL_of_ne (Ne.symm h) _

end GlobalTheory.DefU.InfDecomp

namespace GlobalTheory.DefU


open InfDecomp in
theorem infU_eq_list_prod_embU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n),
    x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧
      (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  intro E _ _ _ n x hx
  classical
  refine ⟨fun v => cutPt v x, fun v => cutPt_mem v x, fun v => ?_, ?_⟩
  · change GeneralLinearGroup.map (coord v.embedding) (cInf (cutPt v x)) =
      GeneralLinearGroup.map (coord v.embedding) (cInf x)
    rw [cInf_cutPt, coord_embedding]
    exact evGL_cutGL_self v (cInf x)
  · refine Subtype.ext (ga_ext ?_ ?_)
    · change cInf (Finset.univ.toList.map fun v => cutPt v x).prod = cInf x
      rw [map_list_prod, List.map_map]
      refine gl_ext_evGL fun w => ?_
      rw [map_list_prod, List.map_map]
      have e : (evGL w ∘ cInf ∘ fun v : InfinitePlace E => cutPt v x) =
          (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) := funext fun v => evGL_cInf_cutPt x v w
      rw [e, list_prod_map_mulSingle w _ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    · let ψ : UA E n →* GL (Fin n) (Af E) := (GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype
      change ψ (Finset.univ.toList.map fun v => cutPt v x).prod = ψ x
      rw [MonoidHom.mem_ker.1 hx, map_list_prod, List.map_map]
      refine List.prod_eq_one fun g hg => ?_
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
      exact MonoidHom.mem_ker.1 (cutPt_mem v x).1

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

open Formalism.L2.DIV GlobalTheory.CoefIrred in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_tensor_coefficient_universal :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V]
      [Module ℂ V] (F : (∀ v, nablaSq ℂ n (lam v)) →ₘₗ[ℂ] V),
      ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V,
        ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  intro ι _ n lam V _ _ F
  have hBasis : ∀ i, bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
    intro i
    apply Subtype.ext
    rw [bVV_coe, tenMul_coe, bVVfun]
    simp only [ssBasis_coe]
  let f := (bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))
  refine ⟨f, ?_, ?_⟩
  · have hComp : f.compMultilinearMap (tenMul lam) = F := by
      apply Module.Basis.ext_multilinear (fun τ => ssBasis ℂ (lam τ))
      intro i
      simp only [LinearMap.compMultilinearMap_apply, ← hBasis, f, Module.Basis.constr_basis]
    intro u
    exact congrArg (fun m => m u) hComp
  · intro g hg
    apply (bVV ℂ lam).ext
    intro i
    simp only [f, Module.Basis.constr_basis]
    rw [hBasis, hg]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CuspRep.GASplit
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_infEq_symm : Continuous (infEq E).symm := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    (continuous_apply w)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_infEq_symm E).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_sInf : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  continuous_const.prodMk continuous_id

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

def splitMulEquiv : GA E a ≃* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toFun g := (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g)
  invFun p := infGL E a p.1 * finGL E a p.2
  left_inv g := infGL_mul_finGL g
  right_inv p := by
    obtain ⟨y, k⟩ := p
    refine Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by simp

def splitEquiv : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toMulEquiv := splitMulEquiv E a
  continuous_toFun :=
    ((continuous_glMap a (pInf E) (continuous_pInf E))).prodMk (continuous_glMap a (pFin E) (continuous_pFin E))
  continuous_invFun :=
    ((continuous_cornerGL a (sInf E) (continuous_sInf E)).comp continuous_fst).mul
      ((continuous_cornerGL a (sFin E) (continuous_sFin E)).comp continuous_snd)

theorem exists_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E),
      ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) :=
  fun E _ _ _ a => ⟨splitEquiv E a, fun _ => rfl⟩

end GlobalTheory.CuspRep.GASplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexExtension
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.RamRational

section General

variable {K V W M N ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}

theorem exists_complex_extension [Fintype ι] (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (hli : LinearIndependent ℂ (fun i => e (b i))) (g : V →ₛₗ[σ] N) :
    ∃ G : M →ₗ[ℂ] N, ∀ x, G (e x) = g x := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℂ (fun i => g (b i))) ∘ₗ hli.repr)
  have hb : ∀ i, G (e (b i)) = g (b i) := by
    intro i
    have hm : e (b i) ∈ Submodule.span ℂ (Set.range (fun i => e (b i))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hG ⟨e (b i), hm⟩
    have h2 : hli.repr ⟨e (b i), hm⟩ = Finsupp.single i 1 := hli.repr_eq_single i _ rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2,
      Finsupp.linearCombination_single, one_smul] at h1
    exact h1
  refine ⟨G, fun x => ?_⟩
  rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, hb, RingHom.id_apply]

theorem mem_span_of_kernel [Fintype ι] {J : Type} [Fintype J] (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (hli : LinearIndependent ℂ (fun i => e (b i)))
    (F : J → M →ₗ[ℂ] M) (hF : ∀ j x, ∃ y, e y = F j (e x)) (m : M)
    (hm : m ∈ Submodule.span ℂ (Set.range (fun i => e (b i)))) (h0 : ∀ j, F j m = 0) :
    m ∈ Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b hli
  let f : J → V →ₗ[K] V := fun j => descend e e hinj (F j) (hF j)
  have hf : ∀ j x, e (f j x) = F j (e x) := fun j x => descend_spec e e hinj (F j) (hF j) x
  let g : V →ₗ[K] (J → V) := LinearMap.pi f
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨h, hh⟩ := LinearMap.exists_extend s
  have hg : ∀ x, g (h (g x)) = g x := by
    intro x
    have h1 : h (g x) = s (g.rangeRestrict x) := LinearMap.congr_fun hh (g.rangeRestrict x)
    have h2 := LinearMap.congr_fun hs (g.rangeRestrict x)
    rw [h1]
    exact congrArg Subtype.val h2
  choose H hH using fun j : J =>
    exists_complex_extension e b hli (e.comp (h ∘ₗ LinearMap.single K (fun _ : J => V) j))
  let P : M →ₗ[ℂ] M := LinearMap.id - ∑ j, H j ∘ₗ F j
  have hP : ∀ x, P (e x) = e (x - h (g x)) := by
    intro x
    have h1 : g x = ∑ j, Pi.single j (f j x) := (Finset.univ_sum_single (g x)).symm
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, map_sub, map_sum, ← hf, hH, LinearMap.coe_single]
  have hPm : P m = m := by
    simp [P, LinearMap.sum_apply, h0]
  rw [← hPm]
  have hle : Submodule.span ℂ (Set.range (fun i => e (b i))) ≤
      (Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0})).comap P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨b i - h (g (b i)), fun j => ?_, (hP _).symm⟩
    have h1 : g (b i - h (g (b i))) = 0 := by rw [map_sub, hg, sub_self]
    have h2 : f j (b i - h (g (b i))) = 0 := congrFun h1 j
    rw [← hf, h2, map_zero]
  exact hle hm

theorem preserves_of_span (e : V →ₛₗ[σ] M) (S : Set V) (hS : Submodule.span K S = ⊤)
    (F : M →ₗ[ℂ] M) (hF : ∀ x ∈ S, ∃ y, e y = F (e x)) (x : V) : ∃ y, e y = F (e x) := by
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hF x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by simp [LinearMap.map_smulₛₗ, ha]⟩

end General

theorem span_ramSub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL]
    {embLL : LL →+* ℂ} {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) :
    Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) = A.Mram := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro m hm
    have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
      (M.emb_basis 0).2.trans M.Fi_zero
    have hrho : ∀ v a x, ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := fun v a =>
      preserves_of_span (M.emb 0) _ (M.lat_good 0).2.2 (A.rhoT v a) (fun x hx => by
        obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx
        exact ⟨y, hy⟩)
    have hNm : ∀ v x, ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
      intro v x
      choose y hy using fun a => hrho v a x
      exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩
    have hall : ∀ x, M.emb 0 x ∈ A.Mu0 := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsp, ← (M.lat 0).b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := mem_span_of_kernel (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm hNm m
      (hsp ▸ hm.1) (fun v => (Submodule.mem_iInf _).1 hm.2 v)
    refine Submodule.span_mono (Set.image_mono ?_) h
    intro x hx
    exact ⟨hall x, (Submodule.mem_iInf _).2 hx⟩

theorem span_ramSub_cols : ∀ (B : Base) (C : Cols B) (u : B.Word),
    Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) =
      (C.mem u).A.Mram :=
  fun _ C u => span_ramSub (C.fm u)

end GlobalTheory.RamRational
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧ ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.LocRet.exists_ret | exact GlobalTheory.DefU.LocRet.exists_ret | (intros; apply GlobalTheory.DefU.LocRet.exists_ret <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS g : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT h : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => BS τ * g τ) (fun τ => BT τ * h τ) f P = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) P) := by
  first | exact @GlobalTheory.FockBaseChange.pureTensorO_subst | exact GlobalTheory.FockBaseChange.pureTensorO_subst | (intros; apply GlobalTheory.FockBaseChange.pureTensorO_subst <;> assumption)
end

