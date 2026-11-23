module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefAtOfPosDef
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

section BaseChange

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

theorem fockS_map_int {s : Type} (P : MvPolynomial s ℤ) (g : MvPolynomial s K) :
    fockS (map φ (map (Int.castRingHom K) P)) (map φ g) = φ (fockS (map (Int.castRingHom K) P) g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockS_eq_sum _ _ (map (Int.castRingHom K) P).support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem pairK_mapVV_int (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (P : MvPolynomial (ι × Fin n × Fin n) ℤ)
    (hx : (x : Pol K ι n) = map (Int.castRingHom K) P) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← map_extremal φ n (lam τ), ← map_extremal (Int.castRingHom K) n (lam τ), fockS_map_int]
  have h5 := fockS_map_int φ P (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1)
  rw [← hx] at h5
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    h5, map_mul, map_div₀, h3, h4]

end BaseChange

def reindexFam {ι M : Type} [Monoid M] (e : ι → ι) : (ι → M) →* (ι → M) :=
  MonoidHom.pi fun τ => Pi.evalMonoidHom (fun _ => M) (e τ)

theorem reindexFam_apply {ι M : Type} [Monoid M] (e : ι → ι) (g : ι → M) (τ : ι) : reindexFam e g τ = g (e τ) := rfl

end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}

theorem exists_coef_round_at (V : HSp D) (hV : ∀ τ, (V.gram.map (tauE D τ)).PosDef)
    (lam : D.what₂.Tau → DomWeight V.rank) (σ : D.what₂.LL →+* ℂ) (p : D.what₂.Tau ≃ D.what₂.Tau)
    (hp : ∀ τ, labE σ τ = tauE D (p τ)) :
    ∃ (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W), c.Is ∧
      (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
        ∀ v, c₁ (rhoVr (labLL D) lam γE v) = c.ρ (γ : GA D V) (c₁ v)) ∧
      (LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL lam a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤ ∧
      ∀ a y, inner ℂ (c₁ (bVV D.what₂.LL lam a)) (c₁ y) = σ (pairVr (labLL D) lam V.gram (bVV D.what₂.LL lam a) y) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨hc, hs⟩ := realGL_laws hθ V
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hG : ∀ τ, (((V.gram.map (tauE D (p τ)))⁻¹)ᵀ).PosDef := fun τ => (hV (p τ)).inv.transpose
  have hlab : ∀ τ x, σ (labLL D τ x) = tauE D (p τ) x := fun τ x => DFunLike.congr_fun (hp τ) x
  refine ⟨coefOf lam hG (invTrK.comp ((reindexFam p).comp (realGL θ V))),
    (toHilb lam hG).toLinearMap.comp (mapVV σ lam), coefOf_is lam hG _ (fun h hh => ?_) (fun h τ => ?_)
      (fun τ => ?_) (fun g hg => ?_), fun γ γE hγ v => ?_, ?_, ?_, fun a y => ?_⟩
  · have : realGL θ V h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom V h) = 1
      rw [show infHom V h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, this, map_one, map_one]
  · exact invTr_unitary (g := realGL θ V h (p τ)) (GlobalTheory.RecDictModel.archM_unitary V (hθ (p τ)) h)
  · refine ((hc (p τ)).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ (p τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (reindexFam p.symm (invTrK g)) fun ρ => by
      have := invTr_unitary (hg (p.symm ρ))
      rwa [p.apply_symm_apply, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (hV ρ).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e]
    refine funext fun τ => ?_
    show inside₂ ℂ _ (inside₂ ℂ _ (g (p.symm (p τ)))) = g τ
    rw [p.symm_apply_apply, invTr_invTr]
  · show toHilb lam hG (mapVV _ lam (rhoK lam (invTrK (embGL (labLL D) γE)) v)) =
      rhoH lam hG (invTrK (reindexFam p (realGL θ V γ))) (toHilb lam hG (mapVV _ lam v))
    have e : (fun τ => Formalism.UG.bc σ (invTrK (embGL (labLL D) γE) τ)) = invTrK (reindexFam p (realGL θ V γ)) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, reindexFam_apply, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    rw [rhoH_toHilb, mapVV_rhoK, e]
  · exact (linearIndependent_mapVV σ lam).map' (toHilb lam hG).toLinearMap (LinearEquiv.ker _)
  · exact span_mapVV σ lam
  · obtain ⟨P, hP⟩ := bVVfun_int D.what₂.LL lam a
    show inner ℂ (toHilb lam hG (mapVV σ lam (bVV D.what₂.LL lam a))) (toHilb lam hG (mapVV σ lam y)) =
      σ (pairK lam (gramKd (labLL D) V.gram) (bVV D.what₂.LL lam a) y)
    rw [inner_toHilb, ← pairK_mapVV_int σ lam _ _ y P ((bVV_coe _ lam a).trans hP)]
    have e : (fun τ => ((V.gram.map (tauE D (p τ)))⁻¹)ᵀ) = fun τ => (gramKd (labLL D) V.gram τ).map σ := by
      funext τ
      have e1 : V.gram.map (tauE D (p τ)) = (V.gram.map (labLL D τ)).map σ := by
        ext a b
        exact (hlab _ _).symm
      have hu : IsUnit (V.gram.map (labLL D τ)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact ((_root_.map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)).isUnit
      rw [gramKd, Matrix.transpose_map, e1]
      congr 1
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg (fun G => pairK lam G (mapVV σ lam (bVV D.what₂.LL lam a)) (mapVV σ lam y)) e

theorem exists_coefAt_of_posDef (i : Fin D.R.m) (h : (Vc D i).IsPosDef) (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) :
    ∃ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ := by
  have hl := (GlobalTheory.GalLift.labels_overK σ).1 hσ
  have hV : ∀ τ, ((Vc D i).gram.map (tauE D τ)).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [h (tauE D τ)] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hg : gramV D i = (Vc D i).gram := by
    rw [gramV, GlobalTheory.StdFrame.neg_eq_false_of_posDef D i h, if_neg Bool.false_ne_true]
  have H := exists_coef_round_at (Vc D i) hV (lamV D i) σ (Equiv.ofBijective _ hl.1).symm fun τ =>
    (congrArg (labE σ) ((Equiv.ofBijective _ hl.1).apply_symm_apply τ).symm).trans (hl.2 _)
  obtain ⟨c, c₁, h1, h2, h3, h4, h5⟩ := H
  exact ⟨c, c₁, h1, h2, h3, h4, fun a b => hg ▸ h5 a _⟩

end GlobalTheory.CoefModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIntegralGaloisRep
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual

namespace GlobalTheory.GalIntegral

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def emb : ↥(OL LL) →+* PadicAlgCl l := LL.1.val.toRingHom.comp (OL LL).val.toRingHom

theorem emb_mem (x : ↥(OL LL)) : emb LL x ∈ LL.1 := (x : ↥LL.1).2

theorem norm_emb_le (x : ↥(OL LL)) : ‖emb LL x‖ ≤ 1 := (Examples₂.LB.mem_OL LL (x : ↥LL.1)).1 x.2

def lift (x : PadicAlgCl l) (hx : x ∈ LL.1) (h : ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx⟩, (Examples₂.LB.mem_OL LL ⟨x, hx⟩).2 h⟩

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

section Main

variable {LL}

def vec {n : ℕ} (v : Fin n → ↥(OL LL)) : Fin n → PadicAlgCl l := fun j => emb LL (v j)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

def stab (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) : Submodule ↥(OL LL) (Fin n → ↥(OL LL)) where
  carrier := {v | ∀ g i, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ 1}
  zero_mem' := by
    intro g i
    have : vec (0 : Fin n → ↥(OL LL)) = 0 := funext fun j => by simp [vec]
    simp [this]
  add_mem' := by
    intro v w hv hw g i
    have : vec (v + w) = vec v + vec w := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_add, Pi.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv g i) (hw g i))
  smul_mem' := by
    intro a v hv g i
    have : vec (a • v) = emb LL a • vec v := funext fun j => by simp [vec]
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, norm_smul]
    exact mul_le_one₀ (norm_emb_le LL a) (norm_nonneg _) (hv g i)

theorem stab_stable (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l))
    (hLL : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) (v : Fin n → ↥(OL LL)) (hv : v ∈ stab LL r) (g : G E Ω) :
    ∃ u ∈ stab LL r, vec u = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := by
  have hmem : ∀ i, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i ∈ LL.1 := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact LL.1.sum_mem fun j _ => LL.1.mul_mem (hLL g i j) (emb_mem LL (v j))
  refine ⟨fun i => lift LL _ (hmem i) (hv g i), ?_, rfl⟩
  intro g' i
  have e : vec (fun i => lift LL _ (hmem i) (hv g i)) = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) := rfl
  rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  exact hv (g' * g) i

theorem bdd [NumberField E] [IsAlgClosure E Ω] (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ B : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ B := by
  let f : G E Ω → ℝ := fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) :=
    (Units.continuous_val (M := Matrix (Fin n) (Fin n) (PadicAlgCl l))).comp hr
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hc.matrix_elem i j).norm
  obtain ⟨B, hB⟩ := (isCompact_range hf).bddAbove
  refine ⟨B, fun g i j => le_trans ?_ (hB ⟨g, rfl⟩)⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j', ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i' j'‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j' => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j'‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

end Main

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

theorem smul_mem_stab [NumberField E] [IsAlgClosure E Ω] (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (hr : Continuous r) :
    ∃ c : ↥(OL LL), emb LL c ≠ 0 ∧ ∀ v : Fin n → ↥(OL LL), c • v ∈ stab LL r := by
  obtain ⟨B, hB⟩ := bdd r hr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  have he : emb LL ((l : ↥(OL LL)) ^ k) = (l : PadicAlgCl l) ^ k := by rw [map_pow, map_natCast]
  refine ⟨(l : ↥(OL LL)) ^ k, ?_, ?_⟩
  · rw [he]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · intro v g i
    have hv : vec (((l : ↥(OL LL)) ^ k) • v) = ((l : PadicAlgCl l) ^ k) • vec v := funext fun j => by
      simp only [vec, Pi.smul_apply, smul_eq_mul, map_mul, he]
    have hX : ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)).mulVec (vec v) i‖ ≤ B := by
      simp only [Matrix.mulVec, dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hB g i i)) fun j _ => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_emb_le LL (v j))).trans (hB g i j)
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, norm_pow, norm_l, inv_pow]
    exact inv_mul_le_one_of_le₀ (hX.trans hk.le) (by positivity)

end Conj

theorem exists_basis {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ} (N : Submodule O (Fin n → O))
    {c : O} (hc : c ≠ 0) (hcN : ∀ v : Fin n → O, c • v ∈ N) : Nonempty (Module.Basis (Fin n) O N) := by
  obtain ⟨m, b0⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) N
  have hm : m = n := by
    have : Module.Finite O N := Module.Finite.of_basis b0
    have h1 : Module.finrank O N = m := by rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
    have h2 := Submodule.finrank_le N
    rw [Module.finrank_fin_fun] at h2
    let φ : (Fin n → O) →ₗ[O] (Fin n → O) :=
      { toFun := fun v j => c * v j
        map_add' := fun v w => funext fun j => mul_add c (v j) (w j)
        map_smul' := fun a v => funext fun j => mul_left_comm c a (v j) }
    have hinj : Function.Injective φ := fun x y hxy => funext fun j => mul_left_cancel₀ hc (congrFun hxy j)
    have h3 : LinearMap.range φ ≤ N := by
      rintro _ ⟨v, rfl⟩
      exact hcN v
    have h4 := Submodule.finrank_mono h3
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at h4
    omega
  exact ⟨b0.reindex (finCongr hm)⟩

theorem sum_repr_map {O K : Type} [CommRing O] [CommRing K] (e : O →+* K) {n : ℕ} {N : Submodule O (Fin n → O)}
    (b : Module.Basis (Fin n) O N) (x : N) (j : Fin n) :
    ∑ k, e ((b k : Fin n → O) j) * e (b.repr x k) = e ((x : Fin n → O) j) := by
  have := congrArg (fun y : N => e ((y : Fin n → O) j)) (b.sum_repr x)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem exists_conj_integral : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  intro E Ω _ _ _ _ _ l _ n LL r hr hLL
  obtain ⟨c, hc0, hcN⟩ := smul_mem_stab LL r hr
  have : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  have hc : c ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  obtain ⟨b⟩ := exists_basis (stab LL r) hc hcN
  have hrep := sum_repr_map (emb LL) b
  let A : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun i j => emb LL ((b j : Fin n → ↥(OL LL)) i)
  let D : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k i => emb LL (b.repr ⟨c • Pi.single i 1, hcN _⟩ k)
  have hAD : A * D = emb LL c • (1 : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    ext j i
    rw [Matrix.mul_apply]
    refine (hrep ⟨c • Pi.single i 1, hcN _⟩ j).trans ?_
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  let Ai : Matrix (Fin n) (Fin n) (PadicAlgCl l) := (emb LL c)⁻¹ • D
  have h1 : A * Ai = 1 := by
    simp only [Ai]
    rw [Matrix.mul_smul, hAD, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Ai * A = 1 := mul_eq_one_comm.1 h1
  let AU : GL (Fin n) (PadicAlgCl l) := ⟨A, Ai, h1, h2⟩
  refine ⟨AU, fun i j => emb_mem LL _, fun i j => ?_, fun g i j => ?_⟩
  · show ((emb LL c)⁻¹ • D) i j ∈ LL.1
    rw [Matrix.smul_apply, smul_eq_mul]
    exact LL.1.mul_mem (LL.1.inv_mem (emb_mem LL c)) (emb_mem LL _)
  · choose u hu hvu using fun j => stab_stable LL r hLL _ (b j).2 g
    let C : Matrix (Fin n) (Fin n) (PadicAlgCl l) := fun k j => emb LL (b.repr ⟨u j, hu j⟩ k)
    have hRA : (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A = A * C := by
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Eq.trans ?_ (hrep ⟨u j, hu j⟩ i).symm
      have h' := congrFun (hvu j) i
      simp only [vec, Matrix.mulVec, dotProduct] at h'
      exact h'.symm
    have hU : ((AU⁻¹ * r g * AU : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) =
        Ai * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * A := by
      simp only [Units.val_mul]
      rfl
    rw [hU, mul_assoc, hRA, ← mul_assoc, h2, one_mul]
    exact norm_emb_le LL _

end GlobalTheory.GalIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMulStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_cofinite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealSmulMemLattice
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  let I : Submodule (𝓞 E) E := L.comap f
  have hI : ∀ s, s ∈ I ↔ s • x ∈ L := fun s => by simp [I, f]
  let π : (Fin n → E) →ₗ[𝓞 E] E := LinearMap.proj (R := 𝓞 E) (φ := fun _ => E) i
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (M := L)
  have hJ : IsFractional (𝓞 E)⁰ (L.map π) := FractionalIdeal.isFractional_of_fg (hfg.map π)
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨L.map π, hJ⟩
  have hle : I ≤ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ (x i)⁻¹ * J :
      FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    intro s hs
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    refine ⟨s * x i, ?_, ?_⟩
    · show s * x i ∈ L.map π
      exact ⟨s • x, (hI s).1 hs, by simp [π]⟩
    · field_simp
  exact ⟨⟨I, FractionalIdeal.isFractional_of_le hle⟩, fun s => hI s⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.VB.Summand

theorem free_of_free_away {R M R' M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (r : R) [IsLocalization.Away r R'] (f : M →ₗ[R] M')
    [IsLocalizedModule (.powers r) f]
    [Module.Free (Localization (.powers r)) (LocalizedModule.Away r M)] : Module.Free R' M' := by
  set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) R').toRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* R'))
    { __ := IsLocalizedModule.iso (.powers r) f, map_smul' := ?_ }
  intro a x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) a
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens}

theorem isFrame_of_affine_basis [G.IsQuasicoherent] (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(G, U)) : IsFrame (F := G) (U := U) b := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  letI := QCoh.resAlgebra (hle.trans h)
  letI := QCoh.resModule G (hle.trans h)
  haveI := QCoh.res_isScalarTower G (hle.trans h)
  let b' := (QCoh.isBaseChange_resLinear G hU hW (hle.trans h)).basis b
  have hb (i : ι) : b' i = resM G (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => resM G (hle.trans h) (b i)) =
      b'.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact b'.equivFun.symm.bijective

theorem exists_frame_of_projective [G.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(G, U)] [Module.Projective Γ(X, U) Γ(G, U)] (y : U) :
    ∃ (V : X.Opens) (n : ℕ) (e : Fin n → Γ(G, V)), (y : X) ∈ V ∧ IsFrame e := by
  have := Module.finitePresentation_of_projective Γ(X, U) Γ(G, U)
  have := hU.isLocalization_stalk y
  have := QCoh.isLocalizedModule_germLinear G hU y
  have hbc := QCoh.isBaseChange_germLinear G hU y
  have : Module.Finite (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .equiv hbc.equiv
  have : Module.Projective (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .of_equiv hbc.equiv
  have : Module.Free (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear G y) (X.presheaf.stalk (y : X))
  have hxf := (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen G hU f
  have : Module.Free Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    free_of_free_away f (QCoh.resBasicOpen G f)
  have : Module.Finite Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    Module.Finite.of_isLocalizedModule (.powers f) (QCoh.resBasicOpen G f)
  exact ⟨_, _, _, hxf, (isFrame_of_affine_basis (hU.basicOpen f)
    (Module.Free.chooseBasis _ _)).comp_equiv (Fintype.equivFin _).symm⟩

end GlobalTheory.VB.Summand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizerStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_involution_similitudeCentralizer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  first | (exact @GlobalTheory.CentSim.centraliser_field_involution) | (exact GlobalTheory.CentSim.centraliser_field_involution) | (intros; apply GlobalTheory.CentSim.centraliser_field_involution  <;> assumption)
end

