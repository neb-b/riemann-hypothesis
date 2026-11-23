module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host

namespace GlobalTheory.HeckeUnrExt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)

theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

def lev (K : Type) [Field K] [NumberField K] (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v⟩

theorem lev_mem_nhds (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) :
    (lev K N : Set (Ideles K)) ∈ nhds (1 : Ideles K) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Ideles K => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Ideles K => (x⁻¹).val.2 := h1.comp continuous_inv
  have h3 : Continuous fun x : Ideles K =>
      (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹ :=
    (h1.sub continuous_const).mul continuous_const
  have hU := ((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_
  · have : ((1 : Ideles K).val.2 - 1) = 0 := sub_self _
    simp only [this, zero_mul]
    exact zero_mem _
  · rintro y ⟨⟨hy, hy'⟩, hy''⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
        congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
    · have e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1 := hy'' v
      haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
      have h0 : Valued.v (N : v.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.2 hN
      rw [map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul] at e
      exact e

noncomputable def crd (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  Units.map ((InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))).toMonoidHom

noncomputable def kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Ideles K →* ℂˣ :=
  ∏ w : InfinitePlace K, crd K w ^ a

theorem coe_kap (K : Type) [Field K] [NumberField K] (a : ℤ) (x : Ideles K) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w (x.val.1 w) ^ a := by
  rw [kap, MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
  rfl

theorem continuous_kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Continuous (kap K a) := by
  have e : (kap K a : Ideles K → ℂˣ) = fun x => ∏ w : InfinitePlace K, (crd K w x) ^ a := by
    funext x
    rw [kap, MonoidHom.finsetProd_apply]
    rfl
  rw [e]
  refine continuous_finsetProd _ fun w _ => Continuous.zpow (f := crd K w) (Continuous.units_map _ ?_) a
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem coe_infDiag' {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    (infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem kap_of_fst {K : Type} [Field K] [NumberField K] (a : ℤ) (x : Ideles K) (k : K)
    (h : x.val.1 = algebraMap K (InfiniteAdeleRing K) k) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, w.embedding k ^ a := by
  rw [coe_kap, h]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [InfiniteAdeleRing.algebraMap_apply]
  simpa using InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)

theorem dense_inf (F : Type) [Field F] [NumberField F] :
    DenseRange (Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) :=
    Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace F, v.Completion)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ :=
    (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact v.ne_zero hk
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem bij_emb (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Bijective fun w : InfinitePlace E => w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  constructor
  · intro w w' h
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, ← InfinitePlace.mk_embedding w,
      ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk]
    exact congrArg _ h
  · intro φ
    refine ⟨InfinitePlace.mk (ComplexEmbedding.lift E φ), ?_⟩
    rcases InfinitePlace.embedding_mk_eq (ComplexEmbedding.lift E φ) with h | h
    · simp only [h, ComplexEmbedding.lift_comp_algebraMap]
    · simp only [h]
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.lift_comp_algebraMap]
      exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal φ)

theorem psi_eq_kap (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E))
    (a : ℤ) (hψ : ψ.IsAlg fun _ => a) (z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ) :
    ψ.1 (Units.map (MonoidHom.inl _ _) z) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
  have c2 : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing (maximalRealSubfield E))
      (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (dense_inf _).induction_on z (isClosed_eq (ψ.2.1.comp c2)
    ((continuous_kap E a).comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E).comp c2))) fun k => ?_
  apply Units.ext
  rw [kap_of_fst a _ (algebraMap _ E (k : maximalRealSubfield E))
    (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap _ E (k : maximalRealSubfield E)))]
  refine Eq.trans ?_ ((hψ k).trans ?_)
  · exact congrArg (fun x => ((ψ.1 x : ℂˣ) : ℂ)) (Units.ext (coe_infDiag' k).symm)
  · exact ((bij_emb E).prod_comp fun φ => φ (k : maximalRealSubfield E) ^ a).symm

open Classical in
theorem prod_type (E : Type) [Field E] [NumberField E] (a : ℤ) (k : E) :
    ∏ w : InfinitePlace E, w.embedding k ^ a =
      ∏ φ : E →+* ℂ, φ k ^ (if (InfinitePlace.mk φ).embedding = φ then a else 0) := by
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_single_of_mem w.embedding (by simp)]
  · rw [InfinitePlace.mk_embedding, if_pos rfl]
  · intro φ hφ hne
    rw [(Finset.mem_filter.1 hφ).2, if_neg hne.symm, zpow_zero]

def levT (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v ∈ T,
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v _ => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v hv => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v hv)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v hv⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v hv => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v hv⟩

theorem lev_le_levT (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    lev K N ≤ levT K T N := fun _ ha => ⟨ha.1, fun v _ => ha.2 v⟩

theorem levT_mem_nhds (K : Type) [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K))) {N : ℕ} (hN : N ≠ 0) :
    (levT K T N : Set (Ideles K)) ∈ nhds (1 : Ideles K) :=
  Filter.mem_of_superset (lev_mem_nhds K hN) (lev_le_levT K T N)

theorem levT_anti (K : Type) [Field K] [NumberField K] {T T' : Set (HeightOneSpectrum (𝓞 K))} (h : T' ⊆ T) (N : ℕ) :
    levT K T N ≤ levT K T' N := fun _ ha => ⟨ha.1, fun v hv => ha.2 v (h hv)⟩

end GlobalTheory.HeckeUnrExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcPt

open GlobalTheory.CplPt GlobalTheory.TopStep GlobalTheory.TopLaw

theorem exists_pt_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2)))
    (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    ∃ (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (κP : GLQ t.X.E (D.R.N t.m2) (rowSG t.Pr t.sel (t.tup μ)))
      (c : rowSG t.Pr t.sel (t.tup μ) → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * ((κP P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) (c P)) ∧
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧
      (∀ P, ((c P : t.X.Kˣ) : t.X.K) * z P = 1) ∧
      (∀ P, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det ((κP P)⁻¹).1 : t.X.Eˣ) : t.X.E) =
        rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) ∧
      ∀ P, InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 ((κP P)⁻¹).1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin _hTie hi β κ p g z hgz
  classical
  have hok := t.idx_ok μ
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp t.m2 P.1 ((t.idx μ).h t.m2 (A.ib t.m2 hi β) P) :=
    fun P => (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let g' : ∀ P : SB t μ, GLint t.X.E (D.R.N t.m2) P.1 := fun P => ⟨g P, hok.int t.m2 _ P (hpr P)⟩
  obtain ⟨q, κP, hN, hf, hfr, hκ⟩ := exists_pt_frames p g'
  have hc : ∀ P, ∃ c : t.X.Kˣ, LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) c ∧
      (c : t.X.K) * z P = 1 := by
    intro P
    obtain ⟨r, hr, hrg, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hmem : redGL _ P.1 (g' P) ∈ ((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H :=
        (hok.grpG t.m2 _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun x hx => redV_redGL (g' P) hx⟩
      have hlam := hok.chrG t.m2 _ ⟨P.1, hP⟩ ⟨_, hmem⟩ (g P) r hr hrg (fun x hx => redV_redGL (g' P) hx)
      have hred : redGL _ P.1 (κP P) = (redGL _ P.1 (g' P))⁻¹ := by
        have h1 := (hκ P).1
        rw [map_mul, map_inv (redGL _ _) (g' P), inv_mul_eq_one, map_inv] at h1
        rw [h1, inv_inv]
      have hmem' : redGL _ P.1 (κP P) ∈ ((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H := hred ▸ inv_mem hmem
      refine ⟨((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).lam ⟨_, hmem'⟩, ⟨fun _ => ⟨hmem', rfl⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      have e : (⟨_, hmem'⟩ : ↥((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).H) = (⟨_, hmem⟩)⁻¹ := Subtype.ext hred
      have ez : z P = ((((t.idx μ).levG t.m2 (A.ib t.m2 hi β) ⟨P.1, hP⟩).lam ⟨_, hmem⟩ : t.X.Kˣ) : t.X.K) := hz.trans hlam.symm
      rw [e, map_inv, ez]
      exact Units.inv_mul _
    · have hQ : P.1 ∈ QE t.sel ((t.tup μ) : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      have hmem : g' P ∈ ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hlam := hok.chrQ t.m2 _ ⟨P.1, hQ⟩ ⟨g' P, hmem⟩ r hr hrg
      have hκe : κP P = (g' P)⁻¹ := by rw [← (hκ P).2 hP, inv_inv]
      have hmem' : κP P ∈ ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H := hκe ▸ inv_mem hmem
      refine ⟨((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).lam ⟨_, hmem'⟩, ⟨fun hP' => absurd hP' hP, fun _ _ => ⟨hmem', rfl⟩⟩, ?_⟩
      have e : (⟨_, hmem'⟩ : ↥((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).H) = (⟨_, hmem⟩)⁻¹ := Subtype.ext hκe
      have ez : z P = ((((t.idx μ).levQ t.m2 (A.ib t.m2 hi β) ⟨P.1, hQ⟩).lam ⟨_, hmem⟩ : t.X.Kˣ) : t.X.K) := hz.trans hlam.symm
      rw [e, map_inv, ez]
      exact Units.inv_mul _
  choose c hc using hc
  refine ⟨q, κP, c, hfr, fun P => (hc P).1, hN, hf, fun P => (hc P).2, fun P => ?_, fun P => ?_⟩
  · by_cases hP : P.1 ∈ t.Pr.vGs
    · have h1 := (hκ P).1
      rw [map_mul, map_inv (redGL _ _) (g' P), inv_mul_eq_one] at h1
      unfold rhoS
      refine unitV_congr _ ((det_glint ((κP P)⁻¹)).2.trans (Eq.trans ?_ (det_glint (g' P)).2.symm))
      rw [← redGL_val, ← redGL_val, h1]
    · rw [(hκ P).2 hP]
  · by_cases hP : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := hok.depthG P hP
      have hq := (GlobalTheory.ColPeriod.levelPrimes t.X t.Pr t.sel t.S (t.tup μ) hPin.fields.ok t.pr_ok hPin.sel P).1.2
      have e : ((κP P)⁻¹).1 = (g' P).1 * ((g' P)⁻¹ * (κP P)⁻¹).1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      unfold InFrame
      rw [e, map_mul]
      refine nearAt_mul _ (hgz P).2 ?_
      rw [hD]
      exact congAt_one_of_redGL t.seam hq ((g' P)⁻¹ * (κP P)⁻¹) (hκ P).1
    · rw [(hκ P).2 hP]
      exact (hgz P).2

end GlobalTheory.LevSrcPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNearAt
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.Approx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAtA_of_val {ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E} (hι : IsAdIso ι) (P : HeightOneSpectrum (𝓞 E))
    (z : AfE F E) (h : Valued.v (ι z P) ≤ 1) : IntAtA (F := F) P z := by
  classical
  set w := ι z with hw
  have hfin : Set.Finite {Q : HeightOneSpectrum (𝓞 E) | w Q ∉ Q.adicCompletionIntegers E} :=
    Filter.eventually_cofinite.1 w.2
  set T := hfin.toFinset with hT
  have hPT : P ∉ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact fun h' => h' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)
  let e : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (w Q))).toNat
  have hbound : ∀ Q ∈ T, ∀ s : 𝓞 E, s ∈ Q.asIdeal ^ e Q →
      Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) * Valued.v (w Q) ≤ 1 := by
    intro Q hQ s hs
    have hQ' : w Q ∉ Q.adicCompletionIntegers E := by rwa [hT, Set.Finite.mem_toFinset] at hQ
    have hne : Valued.v (w Q) ≠ 0 := by
      intro h0
      apply hQ'
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, h0]
      exact zero_le'
    have h1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) := by
      show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 hs
    have h2 : Valued.v (w Q) ≤ WithZero.exp ((e Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      exact Int.self_le_toNat _
    calc _ ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) * WithZero.exp ((e Q : ℕ) : ℤ) := mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert P T)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun Q => if Q = P then 1 else e Q)
    (fun Q _ => Q.prime) (fun Q _ Q' _ hne h' => hne (HeightOneSpectrum.ext h'))
    (fun Q => if Q.1 = P then 1 else 0)
  have hsP : s ∉ P.asIdeal := by
    intro hm
    have h1 := hs P (Finset.mem_insert_self _ _)
    simp only [if_true, pow_one] at h1
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := P.asIdeal.sub_mem hm h1
    simpa using this
  have hsQ : ∀ Q ∈ T, s ∈ Q.asIdeal ^ e Q := by
    intro Q hQ
    have hQP : Q ≠ P := fun h' => hPT (h' ▸ hQ)
    have h1 := hs Q (Finset.mem_insert_of_mem hQ)
    simpa [hQP] using h1
  refine ⟨s, hsP, ?_⟩
  have hmem : iA F E (algebraMap (𝓞 E) E s) * z ∈ RInt F E := by
    refine (hι.2 _).2 fun Q => ?_
    have e1 : ι (iA F E (algebraMap (𝓞 E) E s) * z) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * w Q := by
      rw [map_mul, show ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) from hι.1 _]
      rfl
    rw [e1, map_mul]
    by_cases hQ : Q ∈ T
    · exact hbound Q hQ s (hsQ Q hQ)
    · have hQ' : w Q ∈ Q.adicCompletionIntegers E := by
        by_contra hc
        exact hQ (by rw [hT, Set.Finite.mem_toFinset]; exact hc)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hQ'
      have hs1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ 1 := by
        show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_le_one _ _
      exact mul_le_one' hs1 hQ'
  exact hmem

def compAt (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E where
  toFun a := ι a P
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add (f := _)]; rfl

theorem exists_nearAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N n : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : ∃ g : GL (Fin N) E, NearAt P n y g := by
  classical
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  set Φ := compAt ι P with hΦ
  have hΦi : ∀ x : E, Φ (iA F E x) = algebraMap E (P.adicCompletion E) x := by
    intro x
    show (ι (iA F E x)) P = _
    rw [show ι (iA F E x) = algebraMap E _ x from hι.1 x]
    rfl
  set A : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hA
  set B : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  set qq : P.adicCompletion E := algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹) with hqq
  let S : Set (Matrix (Fin N) (Fin N) (P.adicCompletion E)) :=
    {G | G.det ≠ 0} ∩ ⋂ a : Fin N, ⋂ b : Fin N, {G | Valued.v (qq * (A * G - 1) a b) ≤ 1}
  have hSo : IsOpen S := by
    refine IsOpen.inter (isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const) ?_
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    have hc : Continuous fun G : Matrix (Fin N) (Fin N) (P.adicCompletion E) => qq * (A * G - 1) a b := by
      refine continuous_const.mul ?_
      exact ((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_elem a b
    exact (Valued.isOpen_integer (P.adicCompletion E)).preimage hc
  have hBS : B ∈ S := by
    refine ⟨?_, Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => ?_⟩
    · intro h0
      have := congrArg Matrix.det hAB
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    · show Valued.v (qq * (A * B - 1) a b) ≤ 1
      rw [hAB, sub_self]
      simp
  have hd : DenseRange fun g : Matrix (Fin N) (Fin N) E => g.map (algebraMap E (P.adicCompletion E)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap E P
  obtain ⟨g0, hg0⟩ := hd.exists_mem_open hSo ⟨B, hBS⟩
  obtain ⟨hdet, hcong⟩ := hg0
  have hdet0 : g0.det ≠ 0 := by
    intro h0
    apply hdet
    show (g0.map (algebraMap E (P.adicCompletion E))).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0, fun a b => ?_⟩
  refine intAtA_of_val hι P _ ?_
  have hc : Valued.v (qq * (A * g0.map (algebraMap E (P.adicCompletion E)) - 1) a b) ≤ 1 :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hcong a) b
  refine Eq.trans_le ?_ hc
  congr 1
  show Φ _ = _
  rw [map_mul, hΦi]
  congr 1
  have e1 : ((y⁻¹ * ratA F (Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) * g0.map (iA F E) - 1 := rfl
  rw [e1]
  have e2 : Φ (((((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1 :
      Matrix (Fin N) (Fin N) (AfE F E))) a b) =
      Φ.mapMatrix (((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1) a b := rfl
  have e3 : Φ.mapMatrix (g0.map (iA F E)) = g0.map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hΦi (g0 i j)
  rw [e2, map_sub, map_mul, map_one, e3]

end GlobalTheory.TwU.Approx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteAdmissibleIndepDivisionLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem GlobalTheory.TwU.siteAdm_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  intro D N h u w hg Fl Lv Ch H
  exact H
end

