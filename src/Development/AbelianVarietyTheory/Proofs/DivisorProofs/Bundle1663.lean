module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddings
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifAll

theorem span_range_le {F U H : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H] {σ : F →+* ℂ}
    (j : U →ₛₗ[σ] H) {n : ℕ} (b : Module.Basis (Fin n) F U) :
    Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr u, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_top {F U H H' : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] {σ σ' : F →+* ℂ} (j : U →ₛₗ[σ] H) (j' : U →ₛₗ[σ'] H') {n : ℕ}
    (b : Module.Basis (Fin n) F U) (c : H ≃ₗ⋆[ℂ] H') (hi : LinearIndependent ℂ fun k => j (b k))
    (hs : Submodule.span ℂ (Set.range j') = ⊤) : Submodule.span ℂ (Set.range j) = ⊤ := by
  have h1 : Submodule.span ℂ (Set.range fun k => j' (b k)) = ⊤ := top_le_iff.1 (hs ▸ span_range_le j' b)
  have h2 : Submodule.span ℂ (Set.range fun k => c.symm (j' (b k))) = ⊤ := by
    have h3 := congrArg (Submodule.map (c.symm : H' →ₗ⋆[ℂ] H)) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
  haveI : Module.Finite ℂ H := ⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩
  have h4 : Module.finrank ℂ H ≤ n := by simpa using finrank_le_of_span_eq_top h2
  have h5 : Fintype.card (Fin n) = Module.finrank ℂ H :=
    le_antisymm hi.fintype_card_le_finrank (by simpa using h4)
  refine top_le_iff.1 ((hi.span_eq_top_of_card_eq_finrank' h5).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨b k, rfl⟩

theorem indep_of_conj {H X : Type} [AddCommGroup H] [Module ℂ H] {m : ℕ} (ev : H → X → ℂ)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x) (w : Fin m → H)
    (φ : Fin m → X → ℂ) (hφ : LinearIndependent ℂ φ) (h : ∀ k g, ev (w k) g = starRingEnd ℂ (φ k g)) :
    LinearIndependent ℂ w := by
  let E : H →ₗ[ℂ] (X → ℂ) := { toFun := ev, map_add' := hadd, map_smul' := hsmul }
  rw [Fintype.linearIndependent_iff] at hφ ⊢
  intro a ha k
  have h1 : ∑ k, starRingEnd ℂ (a k) • φ k = 0 := by
    funext g
    have h2 := congrFun (congrArg E ha) g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, Finset.sum_apply] at h2
    have h3 := congrArg (starRingEnd ℂ) h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Pi.zero_apply, map_zero] at h3
    rw [Finset.sum_apply, Pi.zero_apply, ← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    show _ = starRingEnd ℂ (a k * ev (w k) g)
    rw [h, map_mul, Complex.conj_conj]
    rfl
  simpa using hφ _ h1 k

theorem unif_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp hκ hn i σ
  have good := _root_.GlobalTheory.UnifGood.unif_good h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp hκ hn i
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good σ hσ
  obtain ⟨hc, hb⟩ := _root_.GlobalTheory.ConjHilb.conj_hilbert D G Pl0 T0 A T R κ v₀ hM hT
  have hbar := hb (_root_.GlobalTheory.CuspFormValues.jEvExists h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp)
  have hg := good_resC T hσ
  have hV := hT.laws.spaceW _ (inR i) _ hg
  obtain ⟨v, -, hv⟩ := jTop_bar T R κ v₀ hσ hV (hbar i σ hσ hV)
  have ind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb =>
    indep_of_conj (evAt R i σ v) (fun x y => by simp only [evAt, map_add (f := _)]; rfl)
      (fun a x => by simp only [evAt, map_smul]; rfl) _ _
      (GlobalTheory.PhiIndep.phiC_indep D T κ hT.laws i _ hg hV m b hb) fun k g => congrFun (hv (b k)) g
  refine ⟨ind, ?_⟩
  obtain ⟨c⟩ := hc i σ hσ
  obtain ⟨b⟩ := hasB_nTop T hT.laws κ i
  exact span_top _ _ b c (ind _ _ b.linearIndependent) (good ((starRingEnd ℂ).comp σ) hg).2

end GlobalTheory.UnifAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem nsmul_mem_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {x : WO (G.pS p) (G.pT p)} (hx : d.fn x ≠ 0) : k • x ∈ pairLat G p := by
  obtain ⟨x₀, -, h1, hfn⟩ := h
  rw [hfn] at hx
  obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
  rw [nsmul_add]
  exact add_mem h1 (nsmul_mem (nsmul_mem hu k) k)

theorem fn_add_nsmul_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ pairLat G p) (hu' : IsHalf d.e u) (x : WO (G.pS p) (G.pT p)) :
    d.fn (x + k • u) = d.fn x := by
  obtain ⟨x₀, -, -, hfn⟩ := h
  rw [hfn]
  by_cases hx : x ∈ halfCoset d.e (pairLat G p) k x₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]

theorem depthOK_of_isCosetExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  intro D T L sc G W U S t Φ β k τ h
  obtain ⟨-, ⟨e, he, hP, hsum⟩, hcos⟩ := h
  refine ⟨e, he, ⟨hP, hsum⟩, ?_, ?_⟩
  · intro x y hx hy hne
    unfold flatProd at hne
    rw [← hsum x y hx hy] at hne
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    beta_reduce at hne
    have h1 : ∏ j, (d.1 j).fn (x j) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, zero_mul])
    have h2 : ∏ i, (d.2 i).fn (y i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => nsmul_mem_of_isCosetDatum ((hcos d hd).1 j) (h1 j (Finset.mem_univ _)),
      fun i => nsmul_mem_of_isCosetDatum ((hcos d hd).2 i) (h2 i (Finset.mem_univ _))⟩
  · intro x u y v hx hy hu hv
    have hx' : ∀ j, IsHalf e ((x + k • u) j) := fun j a b => by
      show e * (x j + k • u j) a b = (x j + k • u j) a b
      rw [Matrix.add_apply, mul_add, hx j a b, isHalf_nsmul_of k (hu j).1 a b]
    have hy' : ∀ i, IsHalf e ((y + k • v) i) := fun i a b => by
      show e * (y i + k • v i) a b = (y i + k • v i) a b
      rw [Matrix.add_apply, mul_add, hy i a b, isHalf_nsmul_of k (hv i).1 a b]
    unfold flatProd
    rw [← hsum _ _ hx' hy', ← hsum x y hx hy]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hx1 : ∀ j, (d.1 j).fn ((x + k • u) j) = (d.1 j).fn (x j) := fun j =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).1 j) (hu j).2 (((hP d hd).1 j).2.1 ▸ (hu j).1) (x j)
    have hy1 : ∀ i, (d.2 i).fn ((y + k • v) i) = (d.2 i).fn (y i) := fun i =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).2 i) (hv i).2 (((hP d hd).2 i).2.1 ▸ (hv i).1) (y i)
    simp only [hx1, hy1]

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvUniq.LocFin

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev ind (w : Pl (F := F)) : (κ → Fv F w) → ℂ := Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

def archPt (a : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), 0)

theorem evFin_archPt (a : κ → mixedEmbedding.mixedSpace F) (w : Pl (F := F)) (i : κ) : evFin F w (archPt a i) = 0 := by
  change (evalV F w) (0 : Af F) = 0
  exact map_zero _

theorem evI_archPt (a : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPt a i) = a i := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem cancel (v : Pl (F := F)) (g : SInf F κ) (hg : g ≠ 0) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hrt : ∀ ψ₀ : (κ → Fv F v) → ℂ, tens (evFin F v) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update ind v ψ₀))
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hg
    exact ⟨a, by simpa using ha⟩
  have hx0 : r (archPt a) = g a := by
    have e := congrFun (hrt (fun _ => 1)) (archPt a)
    simp only [tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i => evI F (archPt a i)) = a := funext fun i => evI_archPt a i
    have hP : (∏ᶠ w, Function.update (ind (κ := κ)) v (fun _ => 1) w fun i => evFin F w (archPt a i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [evFin_archPt, ind]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrz : r (archPt a + z) = g a := by rw [hr _ z hz, hx0]
  have hev : (fun i => evFin F v ((archPt a + z) i)) = y := by
    funext i
    rw [Pi.add_apply, map_add (f := _), evFin_archPt, zero_add]
    exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun h (archPt a + z)
  simp only [tens, hev, hrz] at e
  exact mul_right_cancel₀ ha e

end GlobalTheory.ThK.EvUniq.LocFin


open scoped Classical in
theorem GlobalTheory.ThK.EvUniq.finRel_of_ev : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → ∀ v, GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v (ev v) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e he ei ev hei hvm hloc v
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d₁) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d₁) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁
    have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    have hevφ : ev v φ ∈ SB _ := by
      rw [← (hvm v).2]
      exact Submodule.mem_map_of_mem hφ
    rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
    exact canc _ _ h1
  · intro u hu hz φ hφ φ₁ hφ₁ hA
    have h1 := he.inv u hu _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    exact canc _ _ h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvUniqInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evFin_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) : evFin F v (z i) = 0 := by
  set u : AF F := LinearMap.inr F (Ainf F) (Af F) 1 with hu
  have h0 : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  have h1 : evFin F v u = 1 := by
    show evalV F v (1 : Af F) = 1
    exact map_one _
  have := congrArg (evFin F v) hzi
  rwa [map_mul, h1, one_mul, map_zero] at this

theorem rest_pure (g : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  rw [Pi.add_apply, map_add (f := _), evFin_eq_zero_of_at z hz v i, add_zero]

theorem eq_of_pure_std (g g' : SInf F κ)
    (h : pure g (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      pure g' (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) : g = g' := by
  refine SchwartzMap.ext fun y => ?_
  let x : κ → AF F := fun i => LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))
  have hI : (fun i => evI F (x i)) = y := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hP : (∏ᶠ v, Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
      (fun i => evFin F v (x i))) = (1 : ℂ) := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    have h0 : (fun i => evFin F v (x i)) = 0 := by
      funext i
      show evalV F v (0 : Af F) = 0
      exact map_zero _
    rw [h0, Set.indicator_of_mem (by intro i; exact zero_mem _)]
    rfl
  have e := congrFun h x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure at e
  rw [hI, hP, mul_one, mul_one] at e
  exact e

end GlobalTheory.ThK.EvUniqInf


open GlobalTheory.ThK.EvUniqInf in
theorem GlobalTheory.ThK.EvUniq.infRel_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' ei := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ _ _ _ hM _ hM₁ e hev ei ev _ hloc0 hloc

  have hex : ∀ v : Pl (F := F), ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => rest_pure g φ hφSB hstd
  have hRest₁ : ∀ g : SInf F (Fin n × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v,
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i)) :=
    fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)
  have he : ∀ g : SInf F (Fin n × Fin d), e (pure g φ) = pure (ei g) (fun v =>
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hloc g φ hφSB hcof, hevφ]
  refine ⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩
  · have h1 := hev.Heisenberg₂ z (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (pure f φ) = pure f₁ φ :=
      hA _ (hRest f)
    rw [h2, he, he] at h1
    have h3 : M₁.co.rho B.ψ z (pure (ei f) (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) = pure g₁ (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :=
      hA₁ _ (hRest₁ (ei f))
    exact eq_of_pure_std _ _ (h1.trans h3)
  · have h1 := hev.inv u hu (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ u (pure f φ) = pure f₁ φ := hA _ (hRest f)
    rw [h2, he, he] at h1
    exact eq_of_pure_std _ _ h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  first | exact @GlobalTheory.GenusTranslate.exists_move_colLat | exact GlobalTheory.GenusTranslate.exists_move_colLat | (intros; apply GlobalTheory.GenusTranslate.exists_move_colLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevelStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  first | exact @GlobalTheory.CongLevelStd.exists_level | exact GlobalTheory.CongLevelStd.exists_level | (intros; apply GlobalTheory.CongLevelStd.exists_level <;> assumption)
end

