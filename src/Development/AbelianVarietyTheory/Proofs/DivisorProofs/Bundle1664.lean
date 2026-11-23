module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvNonzero

theorem pure_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) (hf : f ≠ 0)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := by
  classical
  obtain ⟨yi, hyi⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hS : Set.Finite {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)} :=
    Filter.eventually_cofinite.mp hstd
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  set S := hS.toFinset with hSdef
  let yf : κ → FiniteAdeleRing (𝓞 F) F := fun i =>
    (⟨fun v => if v ∈ S then p v i else 0, by
      apply Filter.eventually_cofinite.mpr
      refine S.finite_toSet.subset ?_
      intro v hv
      by_contra hvS
      apply hv
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      show (if v ∈ S then p v i else 0) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [if_neg hvS']
      exact zero_mem (v.adicCompletionIntegers F)⟩ :
      RestrictedProduct (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
  let x : κ → AdeleRing (𝓞 F) F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i), yf i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  intro hz
  have hx := congrFun hz x
  have h1 : (fun i => evI F (x i)) = yi := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i)) = yi i
    exact RingEquiv.apply_symm_apply _ _
  have h2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ S then p v i else 0 := fun v => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, h1, h2] at hx
  have hg : ∀ v, v ∉ S → φ v (fun i => if v ∈ S then p v i else 0) = 1 := by
    intro v hv
    have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra h
      exact hv (hS.mem_toFinset.mpr h)
    rw [hv']
    have hzero : (fun i : κ => if v ∈ S then p v i else 0) = fun _ => 0 := funext fun i => if_neg hv
    rw [hzero, Set.indicator_of_mem (show (fun _ : κ => (0 : Fv F v)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hsub : Function.mulSupport (fun v => φ v (fun i => if v ∈ S then p v i else 0)) ⊆ S := by
    intro v hv
    by_contra h
    exact hv (hg v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hx
  refine (mul_ne_zero hyi (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)) hx
  have hpv : (fun i : κ => if v ∈ S then p v i else 0) = p v := funext fun i => if_pos hv
  rw [hpv]
  exact hp v

theorem exists_mem_schA_ev_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std, ?_⟩
  rw [hpure f M.vac (fun v => (hM.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.EvNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorEighth
section
noncomputable section

namespace GlobalTheory.GalOne.PhaseAt

section General

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

theorem inner_of_int {K : Type} [Field K] [StarRing K] {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c₁ : VV K lam →ₛₗ[σ] W)
    (pr : VV K lam →ₗ⋆[K] VV K lam →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (bVV K lam a)) (c₁ (bVV K lam a')) = σ (pr (bVV K lam a) (bVV K lam a')))
    (u v : VV K lam) (P : MvPolynomial (I × Fin n × Fin n) ℤ) (hP : (u : Pol K I n) = map (Int.castRingHom K) P) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  have hu : ∀ a, (bVV K lam).repr u a ∈ Formalism.DivisionValues.cmMax K := by
    refine fk_descent _ (bVVfun K lam) (bVVfun_spec K lam).1 (fun k => ?_) _ ?_
    · obtain ⟨Pk, hPk⟩ := bVVfun_int K lam k
      rw [hPk]
      exact fk_int_mem _ _
    · have h := congrArg (fun x : VV K lam => (x : Pol K I n)) ((bVV K lam).sum_repr u)
      simp only [bVV_coe, Submodule.coe_sum, Submodule.coe_smul] at h
      rw [h, hP]
      exact fk_int_mem _ _
  generalize bVV K lam = b at hp hu
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem up_add {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (x y : VV K lam) : GlobalTheory.AdTh.CoefExt.up φ lam (x + y) = GlobalTheory.AdTh.CoefExt.up φ lam x + GlobalTheory.AdTh.CoefExt.up φ lam y :=
  Subtype.ext (map_add (MvPolynomial.map φ) _ _)

theorem up_smul {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (a : K) (x : VV K lam) : GlobalTheory.AdTh.CoefExt.up φ lam (a • x) = φ a • GlobalTheory.AdTh.CoefExt.up φ lam x := by
  apply Subtype.ext
  simp only [GlobalTheory.AdTh.CoefExt.up, Submodule.coe_smul, smul_eq_C_mul, map_mul, map_C]

theorem up_id {K : Type} [Field K] {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n)
    (x : VV K lam) : GlobalTheory.AdTh.CoefExt.up (RingHom.id K) lam x = x :=
  Subtype.ext (MvPolynomial.map_id _)

end General

section Letters

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
open GlobalTheory.AdTh.PhaseMap
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {m n : ℕ} {l : Geo.Tor.Level H} (c : Coeff l)
  (φ : c.F →+* ℂ) {e : D.what₂.Tau → D.what₂.Tau}

abbrev mv (e : D.what₂.Tau → D.what₂.Tau) (lt : LtN Dw n → FVar D m n) : LtN Dw n → FVar D m n :=
  fun ℓ => (e (lt ℓ).1, (lt ℓ).2)

def toG (lt : LtN Dw n → FVar D m n) : MvPolynomial (LtN Dw n) c.F →+* MvPolynomial (FVar D m n) ℂ :=
  (MvPolynomial.rename lt).toRingHom.comp (MvPolynomial.map φ)

variable {lt : LtN Dw n → FVar D m n}

theorem toG_apply (P : MvPolynomial (LtN Dw n) c.F) :
    toG c φ lt P = MvPolynomial.rename lt (MvPolynomial.map φ P) := rfl

theorem toG_X (ℓ : LtN Dw n) : toG c φ lt (MvPolynomial.X ℓ) = MvPolynomial.X (lt ℓ) := by
  simp [toG_apply]

theorem toG_C (a : c.F) : toG c φ lt (MvPolynomial.C a) = MvPolynomial.C (φ a) := by
  simp [toG_apply]

theorem toG_injective (hl : IsLt (mv e lt)) (h : IsTyp D H) : Function.Injective (toG c φ lt) :=
  (MvPolynomial.rename_injective _ fun _ _ hh => hl.injective h (congrArg (fun k : FVar D m n => (e k.1, k.2)) hh)).comp
    (MvPolynomial.map_injective _ φ.injective)

theorem toG_minorP (σ : D.host.E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    toG c φ lt (minorPolynomial c σ i hi col) =
      (Matrix.of fun b s : Fin (i + 1) =>
        (MvPolynomial.X (lt ⟨σ, ⟨s.val, by omega⟩, col b⟩) : MvPolynomial (FVar D m n) ℂ)).det := by
  rw [minorPolynomial, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 b s
  exact toG_X c φ _

theorem toG_pG (he : Function.Bijective e) (hl : IsLt (mv e lt)) (h : IsTyp D H) (hn : Dw.p + Dw.q ≤ n)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hp : ∀ t, p t = Dw.p) (hq : ∀ t, q t = Dw.q)
    (hap : ∀ t k, k < Dw.p → a (tauE D (e t), k) = ap t k)
    (ham : ∀ t k, k < Dw.q → a (conjEmb (tauE D (e t)), k) = am t k) :
    toG c φ lt (pG (Dw := Dw) c a n) = Formalism.IndefR.Datum.delta p q ap am := by
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => conjEmb (tauE D t)) := by
    refine ⟨?_, fun σ => ?_⟩
    · rintro (s | s) (t | t) e
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D e)
      · exact absurd e (h.ne _ _)
      · exact absurd (Eq.symm e) (h.ne _ _)
      · exact congrArg _ (GlobalTheory.SmoothForms.RealPts.tauE_injective D (conjEmb_inj e))
    · by_cases hσ : InPsi H σ
      · obtain ⟨t, ht⟩ := (h.1 σ).1 hσ
        exact ⟨Sum.inl t, ht.symm⟩
      · obtain ⟨t, ht⟩ := (h.2 σ).1 hσ
        exact ⟨Sum.inr t, ht.symm⟩
  have hprod : ∀ f : (D.host.E →+* ℂ) → MvPolynomial (FVar D m n) ℂ,
      ∏ σ, f σ = ∏ t, f (tauE D (e t)) * f (conjEmb (tauE D (e t))) := fun f => by
    rw [← hb.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← he.prod_comp]
    rfl
  rw [pG, map_prod, hprod, Formalism.IndefR.Datum.delta]
  refine Finset.prod_congr rfl fun t _ => ?_
  have m1 := h.mult_pos Dw (e t)
  have m2 := h.mult_neg Dw (e t)
  rw [deltaAt, hp, hq]
  congr 1
  · rw [map_prod]
    conv_rhs => rw [← m1, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.p := lt_of_lt_of_eq i.2 m1
    rw [map_pow, dite_eq_left (by omega), if_pos ((h.1 _).2 ⟨e t, rfl⟩), toG_minorP]
    congr 1
    · rw [minorPlus]
      congr 1
      ext1 b s
      have h1 := hl.pos h (ℓ := ⟨tauE D (e t), ⟨s.val, by have := s.2; omega⟩, Fin.castLE (by omega) b⟩) rfl
      exact X_eq_varF _ (he.1 h1.1) h1.2.1 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (tauE D (e t)) i = _
      rw [aStep, hap t i hi]
      congr 1
      split_ifs with h1
      · exact hap t _ (by omega)
      · rfl
  · rw [map_prod]
    conv_rhs => rw [← m2, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 m2
    rw [map_pow, dite_eq_left (by omega), if_neg ((h.2 _).2 ⟨e t, rfl⟩), toG_minorP]
    congr 1
    · rw [minorMinus]
      congr 1
      ext1 b s
      have h1 := hl.neg h (ℓ := ⟨conjEmb (tauE D (e t)), ⟨s.val, by have := s.2; omega⟩,
        Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)⟩) rfl
      exact X_eq_varF _ (he.1 h1.1) h1.2 (congrArg Fin.val (hl _).1)
    · show aStep Dw a (conjEmb (tauE D (e t))) i = _
      rw [aStep, ham t i hi]
      congr 1
      split_ifs with h1
      · exact ham t _ (by omega)
      · rfl

theorem toG_gaStar (he : Function.Injective e) (hl : IsLt (mv e lt)) (h : IsTyp D H)
    (r1 : ∀ t, relab c φ (tauE D (e t)) = tauE D t) (r2 : ∀ t, relab c φ (conjEmb (tauE D (e t))) = conjEmb (tauE D t))
    (pW : D.what₂.Tau → ℕ) (hp : ∀ t, pW t = Dw.p)
    (ga : Matrix (Fin n) (Fin n) D.host.E) (U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ t a b, (U t)⁻¹ a b = conj (tauE D t (ga b a))) (P : MvPolynomial (LtN Dw n) c.F) :
    toG c φ lt (gaStar c (ga.map (IsCMField.complexConj D.host.E)) P) = PhaseMap.sub pW U (toG c φ lt P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, toG_C, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
  | mul_X P ℓ hP =>
    simp only [map_mul, hP]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [toG_X, gaStar, MvPolynomial.aeval_X, MvPolynomial.aeval_X, letB, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : lt ⟨ℓ.1, ℓ.2.1, j⟩ = ((lt ℓ).1, (lt ℓ).2.1, j) :=
      Prod.ext (he (congrArg Prod.fst (hl.col h ℓ j))) (congrArg Prod.snd (hl.col h ℓ j) :)
    have h0 : (lt ℓ).2.2 = ℓ.2.2 := (hl ℓ).1
    rw [map_mul, toG_C, toG_X, hc, hU, hp, h0]
    congr 2
    show relab c φ ℓ.1 (IsCMField.complexConj D.host.E (ga j ℓ.2.2)) = _
    rw [IsCMField.complexEmbedding_complexConj]
    rcases (hl ℓ).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · replace h2 : ((lt ℓ).2.1 : ℕ) = ℓ.2.1 := h2
      rw [if_pos (h2 ▸ (hl.pos h h1).2.2)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) ((congrArg (relab c φ) h1).trans (r1 _))
    · replace h2 : ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1 := h2
      rw [if_neg (by omega)]
      exact congrArg (fun σ : D.host.E →+* ℂ => conj (σ _)) ((congrArg (relab c φ) h1).trans (r2 _))

end Letters

end GlobalTheory.GalOne.PhaseAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.PhaseAt

open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap

end GlobalTheory.GalOne.PhaseAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CompHS
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def headWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ (i : ℕ) ≤ k then 1 else 0


open Classical in
def tailWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ k < (i : ℕ) then -1 else 0


open Classical in
def unitWt (τ : Psi H) (a : ℤ) : AllWt.Weight Dw := fun τ' _ => if τ' = τ then a else 0

theorem eq_last_add_gaps {N : ℕ} (v : Fin N → ℤ) (hN : 0 < N) (i : Fin N) :
    v i = v ⟨N - 1, by omega⟩ + ∑ k ∈ Finset.range (N - 1), if (i : ℕ) ≤ k then gap v k else 0 := by
  have h := ofGaps_gap v ⟨N - 1, by omega⟩ i
  simp only [ofGaps] at h
  have hi : (i : ℕ) ≤ N - 1 := by omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have e : (Finset.range (N - 1)).filter (fun k => (i : ℕ) ≤ k) = Finset.Ico (i : ℕ) (N - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sub _ hi]
  linarith


open Classical in
def piece (Dw : Datum H) (τ : Psi H) (k : ℕ) : AllWt.Weight Dw :=
  if k + 1 < Dw.p + Dw.q then (if k < Dw.p then headWt τ k else tailWt τ k) else 0

open Classical in
theorem piece_apply (τ τ' : Psi H) (k : ℕ) (i : Fin (Dw.p + Dw.q)) : piece Dw τ k τ' i =
    if τ' = τ then (if k + 1 < Dw.p + Dw.q then (if k < Dw.p then (if (i : ℕ) ≤ k then 1 else 0)
      else (if k < (i : ℕ) then -1 else 0)) else 0) else 0 := by
  unfold piece headWt tailWt
  by_cases h : τ' = τ <;> split_ifs <;> simp_all

open Classical in
theorem unitWt_apply (τ τ' : Psi H) (a : ℤ) (i : Fin (Dw.p + Dw.q)) :
    unitWt τ a τ' i = if τ' = τ then a else 0 := rfl

open Classical in
theorem decomp (la : AllWt.Weight Dw) (hla : GapGe 0 la) (hN : 0 < Dw.p + Dw.q) :
    let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
    la = ∑ x ∈ (Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum (Finset.univ : Finset (Psi H × Bool)),
      (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
        (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat) x) •
      (Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
        (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1)) x) := by
  intro cτ
  classical
  funext τ' i
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_disjSum, Finset.sum_product, Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, piece_apply, unitWt_apply, Fintype.sum_bool,
    mul_ite, mul_zero, if_true, if_false]
  rw [Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, nsmul_eq_mul, Bool.false_eq_true, if_false, mul_one]
  have hv := eq_last_add_gaps (la τ') hN i
  have hterm : ∀ y ∈ Finset.range (Dw.p + Dw.q - 1), (if (i : ℕ) ≤ y then gap (la τ') y else 0) =
      ((gap (la τ') y).toNat : ℤ) * (if y + 1 < Dw.p + Dw.q then (if y < Dw.p then (if (i : ℕ) ≤ y then 1 else 0)
        else (if y < (i : ℕ) then -1 else 0)) else 0) + (if Dw.p ≤ y then gap (la τ') y else 0) := by
    intro y hy
    have hy' : y + 1 < Dw.p + Dw.q := by simp only [Finset.mem_range] at hy; omega
    have hg : 0 ≤ gap (la τ') y := hla τ' y hy'
    rw [Int.toNat_of_nonneg hg, if_pos hy']
    split_ifs <;> first | omega | simp <;> omega
  have hc := Int.toNat_sub_toNat_neg (cτ τ')
  have hcdef : cτ τ' = la τ' ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ') k else 0 := rfl
  rw [hv, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  linarith

end GlobalTheory.NefWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

open GlobalTheory.HeckeUOps

theorem levelLe_one_two {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

theorem exists_betaInv_heckeU {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (_hL : L.Is μ₀) (G : GridData L sc)
    (i j : Fin D.R.m) : ∃ χ : HeckeU D (botBig D i j), ∀ x, χ.f x = (betaH G i j)⁻¹.1 (finIdl D x) := by
  classical
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  choose! qf hqf using _root_.GlobalTheory.FunObj.SqNum.exists_prime_notInert_place G.pl
  have hS : ∀ q ∈ G.pl.S0.image qf, q.Prime ∧ ¬ InertQ D q := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨(hqf v hv).1, (hqf v hv).2.1⟩
  have hlev : ∀ v, (G.ch.chiH (D.R.m - i)).UnrAt v ∨ ∃ q ∈ G.pl.S0.image qf, Formalism.L2.Host.OverP D.host q v ∧
      (G.ch.chiH (D.R.m - i)).LevelLe v 2 := by
    intro PP
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · refine Or.inr ⟨qf _, Finset.mem_image_of_mem _ h, ?_, ?_⟩
      · have := (hqf _ h).2.2
        simpa [HeightOneSpectrum.under, Formalism.L2.Host.OverP] using this
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
        · exact levelLe_one_two (G.ch.lev0 _ k1 k2 PP h0).1
        · exact (G.ch.lev1 _ k1 k2 PP h1).1
    · exact Or.inl (G.ch.unr _ k1 k2 PP h)
  have hcu := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ k1 k2)
  have hci : (G.ch.chiH (D.R.m - i)).HasInf (embT D) (fun τ => 2 * cen D sc.cGap τ (D.R.m - i)) := G.ch.inf _ k1 k2
  let χc : HeckeU D 0 := ofChar 0 _ _ hcu hci (_root_.GlobalTheory.HeckeCont.eq_one_of_cong D _ _ 2 (fun q hq => (hS q hq).1) hlev)
    (_root_.GlobalTheory.NormKill.chi_finIdl_norm_eq_one D _ _ _ 2 (G.ch.triv _ k1 k2) hci (fun q hq => (hS q hq).1) hlev)
    (fun τ => by simp) (_root_.GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt D _ _ 2 hS hlev)
  have he := L.C.isEta
  have hei : L.C.eta.HasInf (embT D) (fun _ => 1) := fun a => by
    rw [he.inf a, ← D.eTau.prod_comp]
    rfl
  let χe : HeckeU D 1 := ofChar 1 L.C.eta _ he.unitary hei (_root_.GlobalTheory.HeckeCont.eq_one_of_cong D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
    (_root_.GlobalTheory.EtaTildeNorm.map_finIdl_norm D _ he) (fun τ => by simp) (_root_.GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
  have hr : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have hx := (ranks_exact D i j).1
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨w, hw⟩ := odd_sLen D
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨inv _ χc (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_zero, mul_one, inv_f]
    rfl
  · refine ⟨inv _ (mul 1 χc χe (by decide)) (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_one, inv_f, mul_f]
    rfl

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSupportedAtStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertDual.latAtV_selfDual | exact GlobalTheory.InertDual.latAtV_selfDual | (intros; apply GlobalTheory.InertDual.latAtV_selfDual <;> assumption)
end

