module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AntitoneOfMemInterl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryGroupCompactQuotient
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.DefU.ClassFin GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.DefiniteTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem herm_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (s : R →+* R) (t : S →+* S)
    (h : ∀ y, p (s y) = t (p y)) (J M : Matrix (Fin n) (Fin n) R) (hM : cT s M * J * M = J) :
    cT t (M.map p) * J.map p * M.map p = J.map p := by
  rw [cT_map p s t h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

abbrev HH (H : Matrix (Fin n) (Fin n) E) : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (AFr E) (sg E) H

theorem AEq_inclR (x : E) : AEq (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) x) = algebraMap E (Af E) x := by
  change toFinAd (Fr E) E ((1 : AFr E) ⊗ₜ[Fr E] x) = _
  rw [toFinAd_tmul, map_one, one_mul]

theorem JR_map (H : Matrix (Fin n) (Fin n) E) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H).map (AEq (E := E)) = H.map (algebraMap E (Af E)) :=
  Matrix.ext fun i j => AEq_inclR (H i j)

def toGLH (H : Matrix (Fin n) (Fin n) E) : HH H →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (AEq (E := E))).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H).subtype

theorem continuous_toGLH (H : Matrix (Fin n) (Fin n) E) : Continuous (toGLH H) := by
  have h1 : Continuous (GeneralLinearGroup.map (AEq (E := E)) : GL (Fin n) _ → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_finAdEquiv)
  exact h1.comp continuous_subtype_val

theorem exists_toGLH (H : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (Af E))
    (hy : y ∈ UJ (conjFin (cc E)) (H.map (algebraMap E (Af E)))) : ∃ t : HH H, toGLH H t = y := by
  let A' : Af E →+* AFr E ⊗[Fr E] E := ((finAdEquiv (Fr E) E).symm : Af E →+* AFr E ⊗[Fr E] E)
  have hy' : cT (conjFin (cc E)) y.val * H.map (algebraMap E (Af E)) * y.val = H.map (algebraMap E (Af E)) := hy
  have hJ : (H.map (algebraMap E (Af E))).map A' = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H := by
    rw [← JR_map]
    exact Matrix.ext fun i j => (finAdEquiv (Fr E) E).symm_apply_apply _
  have hm : GeneralLinearGroup.map A' y ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H := by
    have h := herm_map A' _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) AEq_symm_sig _ _ hy'
    rw [hJ] at h
    exact h
  exact ⟨⟨_, hm⟩, Units.ext (Matrix.ext fun i j => (finAdEquiv (Fr E) E).apply_symm_apply _)⟩

theorem toGLH_rat (H : Matrix (Fin n) (Fin n) E) (t : HH H)
    (ht : t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H) :
    ∃ γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H, toGLH H t = ratF E n γ := by
  obtain ⟨γ₀, hγ₀, e⟩ := ht
  refine ⟨γ₀, hγ₀, Units.ext (Matrix.ext fun i j => ?_)⟩
  have e' : t.1 = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) γ₀ := e.symm
  change AEq (E := E) (t.1.val i j) = algebraMap E (Af E) (γ₀.val i j)
  rw [e']
  exact AEq_inclR _

theorem exists_rat (H : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H) :
    ∃ t : HH H, t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ toGLH H t = ratF E n γ := by
  have hu : cT ((sg E : E →ₐ[Fr E] E) : E →+* E) γ.val * H * γ.val = H := hγ
  have hs : ∀ y : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) ((sg E : E →ₐ[Fr E] E) y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) y) := fun y => by
    change (1 : AFr E) ⊗ₜ[Fr E] _ = Algebra.TensorProduct.map (AlgHom.id (Fr E) (AFr E)) (sg E) ((1 : AFr E) ⊗ₜ[Fr E] y)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hm : Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) γ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H := by
    exact herm_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) hs _ _ hu
  refine ⟨⟨_, hm⟩, ⟨γ, hγ, rfl⟩, Units.ext (Matrix.ext fun i j => ?_)⟩
  exact AEq_inclR _

theorem emb_hform (H : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (x : Fin n → E) :
    φ (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) =
      star (fun i => φ (x i)) ⬝ᵥ (H.map φ).mulVec (fun i => φ (x i)) := by
  have hs : ∀ z : E, φ ((sg E : E →ₐ[Fr E] E) z) = star (φ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E φ z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    Matrix.map_apply, mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  erw [hs]

theorem emb_hform_pos (H : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (hp : (H.map φ).PosDef) (x : Fin n → E)
    (hx : x ≠ 0) : 0 < φ (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) := by
  rw [emb_hform]
  refine hp.dotProduct_mulVec_pos fun h0 => hx (funext fun i => φ.injective ?_)
  simpa using congrFun h0 i

theorem isTotDef (H : Matrix (Fin n) (Fin n) E) (hp : ∀ τ : E →+* ℂ, (H.map τ).PosDef) :
    IsTotDef (sg E) H := by
  refine ⟨inferInstance, fun ι => Or.inl fun x hx => ?_⟩
  letI : Algebra (Fr E) ℂ := (Complex.ofRealHom.comp ι).toAlgebra
  let τ : E →ₐ[Fr E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have he : hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x ∈ maximalRealSubfield E := fun φ => by
    have := emb_hform_pos H φ (hp φ) x hx
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 this).2.symm
  refine ⟨⟨_, he⟩, rfl, ?_⟩
  have h1 := emb_hform_pos H (τ : E →+* ℂ) (hp _) x hx
  have h2 : (τ : E →+* ℂ) (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) = ((ι ⟨_, he⟩ : ℝ) : ℂ) :=
    τ.commutes (⟨_, he⟩ : Fr E)
  rw [h2] at h1
  exact Complex.zero_lt_real.1 h1

theorem isCMExt : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (Fr E) E (sg E) :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ E,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

theorem exists_compact_cover (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) :
    ∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧
      ∀ g ∈ UJ (conjFin (cc E)) (H.map (algebraMap E (Af E))),
        ∃ γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H, ∃ k ∈ C, g = ratF E n γ * k := by
  haveI := GlobalTheory.Mass.topGroup_fin (sg E) H
  have hK := GlobalTheory.Mass.isCompact_stdLevel (sg E) H hnd.2
  have hf := GlobalTheory.Mass.finiteClasses_unitary isCMExt hnd hd hK (GlobalTheory.Mass.isOpen_stdLevel (sg E) H)
  haveI := hf.1
  refine ⟨⋃ q : ClassSet (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H),
    toGLH H '' ((fun k => Quotient.out q * k) '' (GlobalTheory.Mass.stdLevel (sg E) H : Set (HH H))),
    isCompact_iUnion fun q => (hK.image (continuous_const.mul continuous_id)).image (continuous_toGLH H), fun g hg => ?_⟩
  obtain ⟨h, rfl⟩ := exists_toGLH H g hg
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mk_out_eq_mul (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) h
  obtain ⟨γ, hγ, hγe⟩ := toGLH_rat H a⁻¹ (inv_mem ha)
  refine ⟨γ, hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) h,
    ⟨_, ⟨b⁻¹, inv_mem hb, rfl⟩, rfl⟩⟩, ?_⟩
  rw [← hγe, ← map_mul, e]
  congr 1
  group


omit [IsCMField E] in
theorem algebraMap_injective (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

theorem finite_rat_coset (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) (g : HH H) :
    {t : HH H | t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ g⁻¹ * t ∈ GlobalTheory.Mass.stdLevel (sg E) H}.Finite := by
  have hK := GlobalTheory.Mass.isCompact_stdLevel (sg E) H hnd.2
  have hf := GlobalTheory.Mass.finiteClasses_unitary isCMExt hnd hd hK (GlobalTheory.Mass.isOpen_stdLevel (sg E) H)
  haveI := hf.2 1
  have h0 : (Subtype.val '' stabAt (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) 1).Finite :=
    (Set.toFinite _).image _
  by_cases hne : ∃ t₀ : HH H, t₀ ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ g⁻¹ * t₀ ∈ GlobalTheory.Mass.stdLevel (sg E) H
  · obtain ⟨t₀, ht₀, hg₀⟩ := hne
    refine (h0.image fun x => t₀ * x).subset fun t ht => ?_
    refine ⟨t₀⁻¹ * t, ⟨⟨_, mul_mem (inv_mem ht₀) ht.1⟩, ?_, rfl⟩, by group⟩
    have := mul_mem (inv_mem hg₀) ht.2
    change 1⁻¹ * (t₀⁻¹ * t) * 1 ∈ GlobalTheory.Mass.stdLevel (sg E) H
    convert this using 1
    group
  · refine Set.finite_empty.subset fun t ht => hne ⟨t, ht⟩

theorem finite_rat_compact (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) (X : Set (GL (Fin n) (Af E))) (hX : IsCompact X) :
    {γ : GL (Fin n) E | γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H ∧ ratF E n γ ∈ X}.Finite := by
  haveI := GlobalTheory.Mass.topGroup_fin (sg E) H
  haveI : Module.Finite (Fr E) E := Module.Finite.of_restrictScalars_finite ℚ (Fr E) E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField (Fr E)
  let D : Set (Af E) := ⋃ i, ⋃ j, (fun x : GL (Fin n) (Af E) => x.val i j) '' X
  have hD : IsCompact D := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hX.image ((Units.continuous_val.matrix_elem i j))
  obtain ⟨K₀, hK₀, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AFr E) (sg E) H hnd.2
    ((finAdEquiv (Fr E) E).symm '' D) (hD.image continuous_finAdEquiv_symm)
  have hcov := hK₀.elim_nhds_subcover
    (fun g : HH H => {t : HH H | g⁻¹ * t ∈ GlobalTheory.Mass.stdLevel (sg E) H}) fun g _ => by
      refine IsOpen.mem_nhds ((GlobalTheory.Mass.isOpen_stdLevel (sg E) H).preimage (continuous_const.mul continuous_id)) ?_
      change g⁻¹ * g ∈ GlobalTheory.Mass.stdLevel (sg E) H
      rw [inv_mul_cancel]
      exact one_mem _
  obtain ⟨s, -, hs⟩ := hcov
  have hT : ({t : HH H | t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ t ∈ K₀}).Finite := by
    refine (s.finite_toSet.biUnion fun g _ => finite_rat_coset H hnd hd g).subset fun t ht => ?_
    obtain ⟨g, hg, hgt⟩ := Set.mem_iUnion₂.1 (hs ht.2)
    exact Set.mem_iUnion₂.2 ⟨g, hg, ht.1, hgt⟩
  have hinj : Function.Injective (ratF E n) := fun a b hab => Units.ext (Matrix.ext fun i j =>
    algebraMap_injective E (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) hab))
  refine ((hT.image (toGLH H)).preimage hinj.injOn).subset fun γ hγ => ?_
  obtain ⟨t, ht, e⟩ := exists_rat H γ hγ.1
  refine ⟨t, ⟨ht, hKe t fun i j => ?_⟩, e⟩
  refine ⟨(toGLH H t).val i j, Set.mem_iUnion₂.2 ⟨i, j, ratF E n γ, hγ.2, by rw [e]⟩, ?_⟩
  exact (finAdEquiv (Fr E) E).symm_apply_apply _

theorem cocompact_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E),
    IsUnit H.det → cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H → (∀ τ : E →+* ℂ, (H.map τ).PosDef) →
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧
      ∀ g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))),
        ∃ γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H, ∃ k ∈ C, g = ratF E n γ * k) ∧
    ∀ X : Set (GL (Fin n) (Af E)), IsCompact X →
      {γ : GL (Fin n) E | γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ratF E n γ ∈ X}.Finite := by
  intro E _ _ _ n H hu hc hp
  have hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H := ⟨fun i j => congrFun₂ hc i j, hu.ne_zero⟩
  have hd := isTotDef H hp
  exact ⟨exists_compact_cover H hnd hd, fun X hX => finite_rat_compact H hnd hd X hX⟩

end GlobalTheory.CompanionTheory.DefiniteTransport
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylCharEqGtChar
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RmCharacter

open ReciprocityTheory.ChartRestriction.TR.Weyl PositivityTheory.RgBcC

theorem gtChar_zero : ∀ (n : ℕ) (t : Fin n → ℂ), gtChar n (0 : Fin n → ℤ) t = 1
  | 0, _ => by simp [gtChar]
  | n + 1, t => by
    have h : interl (0 : Fin (n + 1) → ℤ) = {(0 : Fin n → ℤ)} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.Icc_self, Finset.mem_singleton]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [gtChar, h, Finset.sum_singleton, gtChar_zero n]
    simp [wsum]

theorem wden_ne_zero {n : ℕ} {t : Fin n → ℂ} (ht : Function.Injective t) : wden n t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.2 fun e => h.ne (ht e)
  · exact one_ne_zero

theorem alt_num {n : ℕ} (lam : Fin n → ℤ) (t : Fin n → ℂ) :
    alt n (lam + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (lam j + (n - 1 - (j : ℕ) : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, delta]
  congr 2
  omega

theorem alt_den {n : ℕ} (t : Fin n → ℂ) :
    alt n ((0 : Fin n → ℤ) + delta n) t = (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det := by
  unfold alt
  congr 1
  refine Matrix.ext fun i j => ?_
  have hj := j.2
  simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, delta, zero_add]
  rw [← zpow_natCast]
  congr 1
  omega

theorem weylChar_eq_gtChar {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) (t : Fin n → ℂ) (h0 : ∀ a, t a ≠ 0)
    (ht : Function.Injective t) : weylChar lam t = gtChar n lam t := by
  have hnum := weylGT ℂ n lam hlam t h0
  have hden := weylGT ℂ n (0 : Fin n → ℤ) (fun _ _ _ => le_rfl) t h0
  rw [gtChar_zero, mul_one, alt_den] at hden
  rw [alt_num] at hnum
  rw [weylChar, ← hnum, ← hden, mul_div_cancel_left₀ _ (wden_ne_zero ht)]

theorem rmChar : RmChar := by
  intro n lam hlam t h0 ht
  have hu : IsUnit (diagonal t : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => h0 a)
  have hw : (dw lam).w = lam := by
    simp only [dw, dif_pos hlam]
  rw [Rm, dif_pos hu, ← LinearMap.trace_eq_matrix_trace, weylChar_eq_gtChar lam hlam t h0 ht,
    GlobalTheory.ContraChar.trace_sqRep_diag (dw lam) _ t rfl, hw]

end GlobalTheory.CompanionTheory.RmCharacter
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

open GlobalTheory.CompanionTheory.BZPhiPG.HpgEmb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_val {a b : ℕ} (e : a = b) (m : Mir k a) (x y : Fin (b + 1)) :
    ((castM k e m : Mir k b) : GL (Fin (b + 1)) k).val x y =
      (m : GL (Fin (a + 1)) k).val (Fin.cast (by omega) x) (Fin.cast (by omega) y) := by
  subst e
  rfl

theorem piPerm_cast (i t : ℕ) (s : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    piPerm i t (Fin.cast (by omega) (ePG i (t + 1) s)) = eGP (i + 1) t s := by
  show eGP (i + 1) t ((ePG i (t + 1)).symm (Fin.cast (by omega) (Fin.cast (by omega) (ePG i (t + 1) s)))) = _
  simp

theorem conj_entry (i t : ℕ) (r : GL (Fin ((i + 1) + t + 1)) k) (x y : Fin ((i + 1) + t + 1)) :
    (wGL k i t * r * (wGL k i t)⁻¹).val (piPerm i t x) (piPerm i t y) = r.val x y := by
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹ * r.val * Equiv.Perm.permMatrix k (piPerm i t)) _ _ = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

theorem conj_block (i t : ℕ) (h : Mir k (i + (t + 1))) (s s' : Σ x, Two (Fin (i + 1)) (Fin (t + 1)) x) :
    (wGL k i t * ((castM k (by omega) h : Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val
        (eGP (i + 1) t s) (eGP (i + 1) t s') =
      (h : GL (Fin (i + (t + 1) + 1)) k).val (ePG i (t + 1) s) (ePG i (t + 1) s') := by
  rw [← piPerm_cast, ← piPerm_cast, conj_entry, castM_val]
  rfl

theorem eta_val (i t : ℕ) (m : Mir k ((i + 1) + t)) (x y : Fin ((i + 1) + t + 1 + 1)) :
    ((wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) :
        GL (Fin ((i + 1) + t + 1 + 1)) k).val x y =
      glEmbMat k ((i + 1) + t + 1) (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x y := by
  have e : wEl k i t * sEmb k ((i + 1) + t) m * (wEl k i t)⁻¹ =
      levi k _ (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  rfl

theorem eta_mem (i t : ℕ) (h : HPG k i (t + 1)) :
    wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈
      HPG k (i + 1) (t + 1) := by
  have hh := mem_parab_iff.1 (show ((h : Mir k (i + (t + 1))) : GL (Fin (i + (t + 1) + 1)) k) ∈ parab k (ePG i (t + 1)) from h.2)
  show ((wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ :
    Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  intro x y b a hxy
  cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
  refine (eta_val i t _ _ _).trans ?_
  rw [ePG_true_eq]
  induction a using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact glEmbMat_cl k _ _ _
  | cast a =>
    rw [ePG_false_castSucc, glEmbMat_cc, conj_block]
    exact hh true false b a hxy

theorem eta_mem_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  intro k _ _ _ _ i t h
  refine ⟨eta_mem i t h, ?_⟩
  have hent : ∀ x z : Fin ((i + 1) + t + 1 + 1),
      ((hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩ : parab k (ePG (i + 1) (t + 1))) :
        GL (Fin ((i + 1) + (t + 1) + 1)) k).val x z =
        glEmbMat k ((i + 1) + t + 1) (wGL k i t * ((castM k (by omega) (h : Mir k (i + (t + 1))) : Mir k ((i + 1) + t)) :
          GL (Fin ((i + 1) + t + 1)) k) * (wGL k i t)⁻¹).val x z :=
    fun x z => eta_val i t _ x z
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) false).val a b =
      glEmbMat k (i + 1) (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) false).val a b
    rw [leviProj_apply, hent]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        exact (glEmbMat_ll k _ _).trans (glEmbMat_ll k _ _).symm
      | cast b =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_lc k _ _ _).trans (glEmbMat_lc k _ _ _).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [ePG_false_last, ePG_false_castSucc]
        exact (glEmbMat_cl k _ _ _).trans (glEmbMat_cl k _ _ _).symm
      | cast b =>
        rw [ePG_false_castSucc, ePG_false_castSucc, glEmbMat_cc, glEmbMat_cc, leviProj_apply, conj_block]
        rfl
  · apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨_, eta_mem i t h⟩) true).val a b =
      (leviProj k (ePG i (t + 1)) (hpgIncl k i (t + 1) h) true).val a b
    rw [leviProj_apply, hent, ePG_true_eq, ePG_true_eq, glEmbMat_cc, leviProj_apply, conj_block]
    rfl

end GlobalTheory.CompanionTheory.BZPhiPG.EtaConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylNotMemClosedCell
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem piPerm_last_val (i t : ℕ) : ((piPerm i t (Fin.last ((i + 1) + t)) : Fin ((i + 1) + t + 1)) : ℕ) = i := by
  have key : ∀ x : Fin (i + (t + 1) + 1), (x : ℕ) = i + 1 + t →
      ((GlobalTheory.BZMir.Leib.eGP (i + 1) t ((GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm x) :
        Fin ((i + 1) + t + 1)) : ℕ) = i := by
    intro x hx
    have hxl : x = Fin.last (i + (t + 1)) := Fin.ext (by rw [Fin.val_last]; omega)
    subst hxl
    have h2 : (GlobalTheory.BZMir.Leib.ePG i (t + 1)).symm (Fin.last (i + (t + 1))) =
        ⟨false, Fin.last i⟩ := by
      rw [Equiv.symm_apply_eq, GlobalTheory.BZMir.Leib.ePG_false_last]
    rw [h2]
    exact GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val (i + 1) t (Fin.last i)
  first
    | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.piPerm, Equiv.trans_apply]; exact key _ rfl)
    | exact key _ rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem wEl_inv_entry (i t : ℕ) (c : Fin ((i + 1) + t + 1)) (hc : (c : ℕ) = i) :
    ((((wEl k i t)⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1 := by
  have hσ : GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t (Fin.last ((i + 1) + t)) = c :=
    Fin.ext ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.piPerm_last_val i t).trans hc.symm)
  rw [GlobalTheory.CompanionTheory.BZPhiPG.wEl, ← map_inv]
  change GlobalTheory.BZMir.glEmbMat k ((i + 1) + t + 1)
      (((GlobalTheory.CompanionTheory.BZPhiPG.wGL k i t)⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
        Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castSucc c) = 1
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
  change Equiv.Perm.permMatrix k (GlobalTheory.CompanionTheory.BZPhiPG.piPerm i t) (Fin.last ((i + 1) + t)) c = 1
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hσ]

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  have h : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  apply Subtype.ext
  change GlobalTheory.BZMir.unip k ((i + 1) + (t + 1))
      (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k))) = 1
  rw [h, ofAdd_zero, map_one]

theorem wEl_notMem_Cl (i t : ℕ) : wEl k i t ∉ Cl k i t := by
  intro hmem
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hmem
  have h := hmem (Fin.last i)
  have hc : (Fin.castLE (by omega) (Fin.last i) : Fin ((i + 1) + t + 1 + 1)) =
      Fin.castSucc (⟨i, by omega⟩ : Fin ((i + 1) + t + 1)) := Fin.ext rfl
  rw [hc, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_inv_entry k i t ⟨i, by omega⟩ rfl] at h
  exact one_ne_zero h

theorem wEl_notMem_Cl_and_dEmb_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), wEl k i t ∉ Cl k i t ∧ dEmb k i t 0 = 1 := by
  intro k _ _ _ _ i t
  exact ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.wEl_notMem_Cl k i t, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.dEmb_zero k i t⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

