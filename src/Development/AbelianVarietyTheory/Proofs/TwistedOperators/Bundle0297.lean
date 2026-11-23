module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLatticeIsometryEqProdLocalComponents
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TwistPC

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ (J.mulVec y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A)
    (M : Matrix (Fin m) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J' (M.mulVec x) (M.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ M * J' * M) x y := by
  rw [hform_eq, hform_eq]
  have e : τ ∘ M.mulVec x = (M.map τ).mulVec (τ ∘ x) := by
    funext i; exact RingHom.map_mulVec τ M x i
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, Matrix.mulVec_transpose,
    dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem comm_comm' (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F (Fv F v) E (Algebra.TensorProduct.comm F E (Fv F v) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem comm_comm'' (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.comm F E (Fv F v) (Algebra.TensorProduct.comm F (Fv F v) E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem comm_sigR' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] Fv F v) :
    Algebra.TensorProduct.comm F E (Fv F v) (Formalism.UG.sigR σ (Fv F v) x) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Algebra.TensorProduct.comm F E (Fv F v) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem locData (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r' → E)) (v : HeightOneSpectrum (𝓞 F))
    (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v)) (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v))
    (k1 : jv * jv' = 1) (k2 : jv' * jv = 1)
    (hiso : Formalism.UG.cT (Formalism.UG.sigR σ (Fv F v)) jv * J'.map (Formalism.UG.inclE (F := F) (Fv F v)) * jv =
      J.map (Formalism.UG.inclE (F := F) (Fv F v)))
    (hlat : jv.mulVec '' (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v)) =
      (Formalism.L2.Herm.locL v Λ' : Set (Fin r' → E ⊗[F] Fv F v))) :
    ∃ jl : GLoc σ J v ≃ₜ* GLoc σ J' v, IsLatticeConj Λ Λ' jl ∧ ∀ g,
      (GlobalTheory.AdelicU.matHom _ σ J' (jl g)).val =
        jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * (GlobalTheory.AdelicU.matHom _ σ J g).val *
          jv'.map (Algebra.TensorProduct.comm F E (Fv F v)) := by
  obtain ⟨cm, hcm⟩ : ∃ cm : E ⊗[F] Fv F v →+* Fv F v ⊗[F] E,
      cm = (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : Fv F v ⊗[F] E →+* E ⊗[F] Fv F v,
      cb = (Algebra.TensorProduct.comm F (Fv F v) E).toRingEquiv.toRingHom := ⟨_, rfl⟩
  have ecm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      X.map (Algebra.TensorProduct.comm F E (Fv F v)) = X.map cm := by
    intro m k X; subst hcm; rfl
  have bc1 : ∀ x, cb (cm x) = x := fun x => by subst hcm hcb; exact comm_comm' v x
  have bc2 : ∀ x, cm (cb x) = x := fun x => by subst hcm hcb; exact comm_comm'' v x
  have bcm : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)), (X.map cm).map cb = X := by
    intro m k X; ext i l; exact bc1 _
  simp only [ecm]
  have hab : jv.map cm * jv'.map cm = 1 := by rw [← Matrix.map_mul, k1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hba : jv'.map cm * jv.map cm = 1 := by rw [← Matrix.map_mul, k2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (jv.map cm) * JR (F := F) (Fv F v) J' * jv.map cm =
      JR (F := F) (Fv F v) J := by
    have e := congrArg (fun X => X.map cm) hiso
    simp only [Matrix.map_mul] at e
    convert e using 3
    · ext i k; subst hcm; exact (comm_sigR' σ v _).symm
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · ext i k; subst hcm; simp [JR, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry σ J J' v _ _ hab hba hJ
  refine ⟨φ, ?_, hφ⟩
  have injv : Function.Injective jv.mulVec := fun x y hxy => by
    have := congrArg jv'.mulVec hxy
    simpa [Matrix.mulVec_mulVec, k2] using this
  have hA : (jv.map cm).map cb = jv := bcm jv
  refine ⟨LinearEquiv.ofLinear (Matrix.mulVecLin (jv.map cm)) (Matrix.mulVecLin (jv'.map cm))
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hab])
    (LinearMap.ext fun x => by simp [Matrix.mulVec_mulVec, hba]), fun y y' => ?_, fun y => ?_, fun g y => ?_⟩
  · show GlobalTheory.AdelicU.hLin σ J' (Fv F v) ((jv.map cm).mulVec y) ((jv.map cm).mulVec y') = GlobalTheory.AdelicU.hLin σ J (Fv F v) y y'
    unfold GlobalTheory.AdelicU.hLin hR
    rw [hform_mulVec, hJ]
  · show (jv.map cm).mulVec y ∈ GlobalTheory.AdelicU.latLoc F Λ' v ↔ y ∈ GlobalTheory.AdelicU.latLoc F Λ v
    have ecb : ∀ {m : ℕ} (z : Fin m → Fv F v ⊗[F] E),
        (fun i => Algebra.TensorProduct.comm F (Fv F v) E (z i)) = cb ∘ z := by
      intro m z; subst hcb; rfl
    rw [_root_.GlobalTheory.TwistLat.mem_latLoc_iff_comm_mem_locL, _root_.GlobalTheory.TwistLat.mem_latLoc_iff_comm_mem_locL, ecb, ecb]
    have e : cb ∘ (jv.map cm).mulVec y = jv.mulVec (cb ∘ y) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hA]
    rw [e]
    have := injv.mem_set_image (s := (Formalism.L2.Herm.locL v Λ : Set (Fin r → E ⊗[F] Fv F v))) (a := cb ∘ y)
    rw [hlat] at this
    exact this
  · show (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val.mulVec ((jv.map cm).mulVec y) =
      (jv.map cm).mulVec ((GlobalTheory.AdelicU.matHom _ σ J g).val.mulVec y)
    rw [hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hba, Matrix.mul_one]

theorem assemble (v : HeightOneSpectrum (𝓞 F)) {r r' : ℕ} (jv : Matrix (Fin r') (Fin r) (E ⊗[F] Fv F v))
    (jv' : Matrix (Fin r) (Fin r') (E ⊗[F] Fv F v)) (M : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)) :
    jv * M.map (Algebra.TensorProduct.comm F (Fv F v) E) * jv' =
      (jv.map (Algebra.TensorProduct.comm F E (Fv F v)) * M * jv'.map (Algebra.TensorProduct.comm F E (Fv F v))).map
        (Algebra.TensorProduct.comm F (Fv F v) E) := by
  have e : ∀ {m k : ℕ} (X : Matrix (Fin m) (Fin k) (E ⊗[F] Fv F v)),
      (X.map (Algebra.TensorProduct.comm F E (Fv F v))).map (Algebra.TensorProduct.comm F (Fv F v) E) = X := by
    intro m k X; ext i l; exact comm_comm' v _
  rw [Matrix.map_mul, Matrix.map_mul, e, e]

end Gen


set_option maxHeartbeats 3000000 in
theorem isom_locComponents : ∀ (D : D7) (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Φ₀ : GfC V ≃ₜ* GfC V'), GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V' (frameLat V) (frameLat V') j → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy V V' j Φ₀ → ∃ jl : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (jl v)) ∧ ∀ v g, Φ₀ (locFin V v g) = locFin V' v (jl v g) := by
  intro D V V' j Φ₀ hj hΦ
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  have key := fun v => locData D.sp.cm.sig V.gram V'.gram (frameLat V) (frameLat V') v
    (j.map (Formalism.UG.prV (E := D.host.E) v)) (j'.map (Formalism.UG.prV (E := D.host.E) v))
    (GlobalTheory.HeckeTrans.map_mul_one _ h1) (GlobalTheory.HeckeTrans.map_mul_one _ h2)
    (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).1.2 (GlobalTheory.FinAdIdent.isLocLatIsom_map hj v).2
  choose jl hjl hjm using key
  refine ⟨jl, hjl, fun v g => ?_⟩
  apply GlobalTheory.T.finiteAdelicUnitaryPoint_ext_localComponents
  intro u
  have hc := hΦ (locFin V v g)
  have e1 := congrArg (fun X => GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul X j') hc
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.mmul, Matrix.mul_assoc, h1, Matrix.mul_one] at e1
  rw [e1, Matrix.map_mul, Matrix.map_mul]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V u g, GlobalTheory.T.finitePart_localToFiniteAdelic_component_self V' u (jl u g), hjm]
    rw [← Matrix.mul_assoc]
    exact assemble (F := D.host.F) (E := D.host.E) u _ _ _
  · rw [GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V hu, GlobalTheory.T.finitePart_localToFiniteAdelic_component_ne V' hu, Matrix.one_mul, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.TwistPC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
section
noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def algAt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = M.vac v) ∧ Φ = pure f φ}

variable (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)

theorem algAt_mono {T T' : Finset (Pl F)} (h : T ⊆ T') : algAt M ψ emb T ≤ algAt M ψ emb T' := by
  refine Submodule.span_mono ?_
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨f, φ, hf, hφ, fun v hv' => hv v fun h' => hv' (h h'), rfl⟩

theorem exists_algAt {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb)
    (T₀ : Finset (Pl F)) : ∃ T, T₀ ⊆ T ∧ Φ ∈ algAt M ψ emb T := by
  classical
  induction hΦ using Submodule.span_induction generalizing T₀ with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hco, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hco
    refine ⟨T₀ ∪ hfin.toFinset, Finset.subset_union_left, Submodule.subset_span ⟨f, φ, hf, hφ, fun v hv => ?_, rfl⟩⟩
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne))
  | zero => exact ⟨T₀, subset_rfl, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    obtain ⟨T₂, h₂, hy₂⟩ := hy T₁
    exact ⟨T₂, h₁.trans h₂, add_mem (algAt_mono M ψ emb h₂ hx₁) hy₂⟩
  | smul c x _ hx =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    exact ⟨T₁, h₁, Submodule.smul_mem _ c hx₁⟩

end GlobalTheory.HoweGlobal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyEqOfMemHomFinDS
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

theorem exists_clm_of_inner_eq {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (v : ι → H) (v' : ι → K) (c : ℂ) (hc : ∀ i j, ⟪v' i, v' j⟫_ℂ = c * ⟪v i, v j⟫_ℂ)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    ∃ A : H →L[ℂ] K, ∀ i, A (v i) = v' i := by
  set p := Finsupp.linearCombination ℂ v with hp
  set p' := Finsupp.linearCombination ℂ v' with hp'
  have hin : ∀ f f', ⟪p' f, p' f'⟫_ℂ = c * ⟪p f, p f'⟫_ℂ := by
    intro f f'
    simp only [p, p', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hn : ∀ f, ‖p' f‖ = Real.sqrt ‖c‖ * ‖p f‖ := by
    intro f
    have h := congrArg norm (hin f f)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, norm_pow] at h
    simp only [RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm] at h
    rw [← Real.sqrt_sq (norm_nonneg (p' f)), h, Real.sqrt_mul (norm_nonneg c), Real.sqrt_sq (norm_nonneg _)]
  have hker : LinearMap.ker p ≤ LinearMap.ker p' := fun f hf => by
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← norm_eq_zero, hn, hf, norm_zero, mul_zero]
  let L : LinearMap.range p →ₗ[ℂ] K := (LinearMap.ker p).liftQ p' hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap
  have hL : ∀ f, L ⟨p f, f, rfl⟩ = p' f := fun f => by
    have : p.quotKerEquivRange.symm ⟨p f, f, rfl⟩ = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hb : ∀ x, ‖L x‖ ≤ Real.sqrt ‖c‖ * ‖x‖ := by
    rintro ⟨_, f, rfl⟩
    rw [hL, hn]; rfl
  let A0 := L.mkContinuous _ hb
  let e := (LinearMap.range p).subtypeL
  have hrange : (LinearMap.range p : Set H) = Submodule.span ℂ (Set.range v) := by
    rw [hp, Finsupp.range_linearCombination]
  have hdense : DenseRange e := by
    have : Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H) :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
    rw [← hrange] at this
    exact this.denseRange_val
  have hui : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨A0.extend e, fun i => ?_⟩
  have h1 : p (Finsupp.single i 1) = v i := by simp [p]
  have h2 : p' (Finsupp.single i 1) = v' i := by simp [p']
  have := ContinuousLinearMap.extend_eq A0 hdense hui ⟨p (Finsupp.single i 1), _, rfl⟩
  simp only [e, Submodule.subtypeL_apply, A0, LinearMap.mkContinuous_apply, hL] at this
  rw [← h1, this, h2]

end GlobalTheory.TrExt

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

theorem apply_eq_of_mem_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type}
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {ρ : GA D V →* (X →L[ℂ] X)} {U : Submodule ℂ X}
    {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H X} (h : T ∈ homFinDS σ M ρ U) (g : GA D V) (w : W)
    (y : ∀ τ, M.H τ) : ρ g (T w y) =
      T (σ (toFin V g) w) (fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ)) := by
  classical
  have hm := mem_homTensorPi.1 h
  conv_lhs => rw [← toInf_mul_toFin g, map_mul, ContinuousLinearMap.mul_apply]
  have h1 : ρ (toFin V g : GA D V) (T w y) = T (σ (toFin V g) w) y := (hm.2.1 (toFin V g) w y).symm
  rw [h1]
  exact _root_.GlobalTheory.TrAct.toInf_apply_homDS D V S M X ρ U _ (h.1 _) g y


open Classical in
theorem exists_homIn_extend : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : GA D V →* (K →L[ℂ] K)), IsUnitaryRep ρ → ∀ U : Submodule ℂ K, IsClosed (U : Set K) → ∀ T' ∈ homFinDS σ M ρ U, ∃ A ∈ homIn π ρ U, ∀ w y, A (T w y) = T' w y := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ π hπ T hT hinj hd K _ _ _ ρ hρ U hU T' hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hTw : ∀ w, T w ∈ homDS M π ⊤ := fun w => hT.1 w
  have hTw' : ∀ w, T' w ∈ homDS M ρ U := fun w => hT'.1 w
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T' w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hπ (hTw x) ((map_ne_zero_iff T hinj).2 hx)
  have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
    change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
    rw [hTm.2.1, hTm.2.1, inner_map_map hπ]
  have hC : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g x y => by
    change ⟪T' (σ g y) _, T' (σ g x) _⟫_ℂ = ⟪T' y _, T' x _⟫_ℂ
    rw [hTm'.2.1, hTm'.2.1, inner_map_map hρ]
  obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hCB⟩ := _root_.GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W σ σ hadm hadm.1 B C hBpos hB hC
  obtain ⟨c, rfl⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K₀ hKo hKc W σ hirr hadm φ hφ

  have hbe : ∀ x y, bePi (T' x) (T' y) = conj c * bePi (T x) (T y) := fun x y => by
    have : bePi (T' x) (T' y) = bePi (T x) (T (c • y)) := hCB x y
    rw [this, map_smul, bePi, bePi, ContinuousMultilinearMap.smul_apply, inner_smul_left]
  have hinner : ∀ q r : W × (∀ τ, M.H τ), ⟪T' q.1 q.2, T' r.1 r.2⟫_ℂ = conj c * ⟪T q.1 q.2, T r.1 r.2⟫_ℂ := by
    rintro ⟨w, y⟩ ⟨w', y'⟩
    rw [inner_eq_bePi hδ hρ (hTw' w') (hTw' w), inner_eq_bePi hδ hπ (hTw w') (hTw w), hbe, mul_assoc]
  have hset : {v | ∃ w y, v = T w y} = Set.range (fun q : W × (∀ τ, M.H τ) => T q.1 q.2) := by
    ext v; constructor
    · rintro ⟨w, y, rfl⟩; exact ⟨(w, y), rfl⟩
    · rintro ⟨⟨w, y⟩, rfl⟩; exact ⟨w, y, rfl⟩
  rw [hset] at hd
  obtain ⟨A, hA⟩ := exists_clm_of_inner_eq _ _ _ hinner hd
  have hA' : ∀ w y, A (T w y) = T' w y := fun w y => hA (w, y)
  have hdense : Dense ((Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2)) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  refine ⟨A, ⟨fun x => ?_, fun g => ?_⟩, fun w y => hA (w, y)⟩
  · have hle : Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2) ≤ U.comap (A : H →ₗ[ℂ] K) :=
      Submodule.span_le.2 (by
        rintro _ ⟨⟨w, y⟩, rfl⟩
        show A (T w y) ∈ U
        rw [show A (T w y) = T' w y from hA (w, y)]
        exact hTm'.1 w y)
    have := Submodule.topologicalClosure_minimal _ hle (hU.preimage A.continuous)
    rw [hd] at this
    exact this trivial
  ·
    refine DFunLike.congr_fun (ContinuousLinearMap.ext_on (f := A ∘L π g) (g := ρ g ∘L A) hdense ?_)
    rintro _ ⟨⟨w, y⟩, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [apply_eq_of_mem_homFinDS hT, hA', hA', apply_eq_of_mem_homFinDS hT']

end GlobalTheory.TrExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacTransfer

variable {D : D7} {S X : HSp D} {n d : ℕ}

def archLine (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) : ℝ →+ WO S X where
  toFun t := cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
  map_zero' := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_zero]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 • u) = 0
    rw [h, zero_smul]
    exact map_zero cS
  map_add' s t := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_add (f := _)]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) • u) =
      cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) + cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
    rw [h, add_smul]
    exact map_add cS _ _

theorem archLine_apply (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) (t : ℝ) :
    archLine cS u t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) := rfl

end GlobalTheory.VacTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspApprox

open MeasureTheory Matrix Formalism.REAL GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem avgN_weighted_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau)
    (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) →
        ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  intro D θ hθ N τ e he a
  set P := N.M.fr τ with hPdef
  have hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun k =>
    GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P :=
    (continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const
  have hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ N.V τ).comp_continuous hκ hU
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn
  have hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H| := fun k => by
    have h := hH k (Set.mem_univ k)
    simp only [Function.comp_apply, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hne : Continuous fun k => ‖e k‖ := he.norm
  refine ⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩
  have hq := quotHeight_pos N.V g
  have hqa : 0 < quotHeight N.V g ^ a := pow_pos hq a
  have hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤
      ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) := by
    intro k
    set A := atTau θ N.V τ (P⁻¹ * toMK k * P)
    have h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H| := by
      have h := quotHeight_mul_le N.V (g * A) A⁻¹
      rw [mul_inv_cancel_right, height_inv] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)
    have h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hq.le h1 a
    have h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a :=
      calc ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ ‖f (g * A)‖ * (quotHeight N.V (g * A) ^ a * |H| ^ a) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (‖f (g * A)‖ * quotHeight N.V (g * A) ^ a) * |H| ^ a := by ring
        _ ≤ B * |H| ^ a := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_div_iff₀ hqa]; exact h3
  have hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤
      ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ)) :=
    norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const))
      (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const] at hint
  calc ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * quotHeight N.V g ^ a
      ≤ ((∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * (B * |H| ^ a / quotHeight N.V g ^ a)) * quotHeight N.V g ^ a :=
        mul_le_mul_of_nonneg_right hint hqa.le
    _ = (∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a * B := by field_simp

end GlobalTheory.KFinCuspApprox

end
end

