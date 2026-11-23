module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Formalism.LocalToGlobal.NumberFieldFamilies.EvRowSurjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChains
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainComparisonTransferOtherLaterStagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainComparison_transfer_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  first | exact @GlobalTheory.Mem.R3.Rw.chT_tr | exact GlobalTheory.Mem.R3.Rw.chT_tr | (intros; apply GlobalTheory.Mem.R3.Rw.chT_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColRecCEvBijective
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev cstT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) : LocCst B.fields (rowSG (B.primes X) I.sel τ) :=
  twCst I.Ch I.sel τ I.glob

abbrev idxT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) :
    ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) :=
  twIdx I.Ch I.sel τ (cstT I τ) (B.R.m - 2)

variable {I}

theorem cstT_tup (ht : I.IsTw) (a : I.ι) : cstT I (I.tup a) = I.cst a := (ht.cst_eq a).symm

theorem idxT_tup (ht : I.IsTw) (a : I.ι) : idxT I (I.tup a) = I.idx a := (ht.idx_eq a).symm

theorem of_forall_ix (ht : I.IsTw) {U : Set I.ι}
    (p : ∀ τ : Tup B.fields.F B.fields.E B.fields.K I.S, LocCst B.fields (rowSG (B.primes X) I.sel τ) →
      ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) → Prop)
    (hp : ∀ a, p (I.tup a) (I.cst a) (I.idx a)) (t : TupU I U) : p t.1 (cstT I t.1) (idxT I t.1) := by
  rw [← tup_ixOf I t, cstT_tup ht, idxT_tup ht]
  exact hp _

theorem idxT_ok (h : I.Ok) (ht : I.IsTw) {U : Set I.ι} (t : TupU I U) :
    (idxT I t.1).Ok I.Ch I.sel t.1 (cstT I t.1) I.glob (B.R.m - 2) :=
  of_forall_ix ht (fun τ c L => L.Ok I.Ch I.sel τ c I.glob (B.R.m - 2)) h.idx_ok t

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)

def colRecC : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) where
  Pr := B.primes X
  Rk := B.R
  W := B.wts
  Ch := I.Ch
  sel := I.sel
  Sg := I.S
  hX := hX
  Lv := rPsymF (R := B.R) I.Ch
  Xg := Xg
  m2 := B.R.m - 2
  Gc := I.glob
  mu := fun t => t.1
  cst := fun t => cstT I t.1
  Li := fun t => idxT I t.1
  hL := fun t => idxT_ok h ht t
  hP := fun t => mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel t.1 hX _
  Mem := B.Word
  wd := fun u => u
  b := fun t _ => (idxT_ok h ht t).last_uniq.choose
  hY := fun t u => coupling_index_set_finite (Pr := B.primes X) I.sel t.1 (cstT I t.1) (idxT I t.1) u (B.R.m - 2) _
  Am := I.J.amb B χ
  hK := fun t u => of_forall_ix ht
    (fun τ c L => ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel τ c L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).2.2.2) t _ _
  hF := fun t u => of_forall_ix ht (fun τ _ L => ∀ j, (chF (Pr := B.primes X) B.wts I.sel τ L u j).Ok)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).1) t
  hE := fun u => by
    have e := RcHyp.evaluationDatum_ok_baseTuple I u
    rw [I.trueColumn_tuple_trivial_eq_one] at e
    exact e
  ev := evC (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
    (rPsymF (R := B.R) I.Ch)

end GlobalTheory.Mem.R3.SelC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruenceOneMatricesMemNhdsOne
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.Mem.ColAd.Nbhd

theorem pi_small {ι T : Type} [Finite ι] [TopologicalSpace T] (x : T) (W : Set (ι → T))
    (hW : W ∈ nhds (fun _ : ι => x)) : ∃ O ∈ nhds x, ∀ X : ι → T, (∀ i, X i ∈ O) → X ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun X hX => hsub fun i _ => Set.mem_iInter.1 (hX i) i⟩

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem exists_nsmul_intAf : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ O ∈ nhds (0 : AfE F E), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Formalism.L2.Herm.intAf F E, N • x ∈ O := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro O hO
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  have hc : Continuous (rlt_comb (F := F) b) := IsModuleTopology.continuous_of_linearMap _
  have h1 : (rlt_comb (F := F) b) ⁻¹' O ∈ nhds (0 : Fin m → FiniteAdeleRing (𝓞 F) F) :=
    hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hO)
  obtain ⟨O', hO', hsub⟩ := pi_small (0 : FiniteAdeleRing (𝓞 F) F) _ h1
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O' hO'
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨r, hr, rfl⟩ := (Set.ext_iff.1 (rlt_image_comb (F := F) b hb) x).2 hx
  rw [← map_nsmul]
  exact hsub _ fun j => hNO (r j) (hr j (Set.mem_univ _))

end Tens

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem mem_of_congOne_entry {m₀ m : ℕ} (hdvd : m₀ ∣ m) (hm : 0 < m) (x : AfE F E)
    (hx : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m : ℕ) : 𝓞 E))⁻¹ * x ∈
      Formalism.L2.Herm.intAf F E) : ∃ y ∈ Formalism.L2.Herm.intAf F E, x = m₀ • y := by
  obtain ⟨q, rfl⟩ := hdvd
  set s := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E))⁻¹ * x with hs
  have hm' : (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hm.ne'
  have hx' : x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) * s := by
    rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hm', map_one, one_mul]
  refine ⟨(q : AfE F E) * s, mul_mem (natCast_mem _ q) hx, ?_⟩
  have hc : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E ((m₀ * q : ℕ) : 𝓞 E)) =
      ((m₀ * q : ℕ) : AfE F E) := by
    rw [map_natCast, map_natCast]
  rw [hx', hc, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

theorem congOne_nhds : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  intro F E _ _ _ _ _ n
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := rlt_isModTop F E
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AfE F E)
  intro N hN
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hN
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hN
  let φ : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E) →
      Matrix (Fin n) (Fin n) (AfE F E) × (Matrix (Fin n) (Fin n) (AfE F E))ᵐᵒᵖ :=
    fun p => ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.1,
      MulOpposite.op ((1 : Matrix (Fin n) (Fin n) (AfE F E)) + Matrix.of p.2))
  have hφ : Continuous φ :=
    (continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))
  have hφ0 : φ (0, 0) = Units.embedProduct _ 1 := by
    rw [map_one]
    simp [φ]
  have h1 : φ ⁻¹' t ∈ nhds ((0, 0) : (Fin n → Fin n → AfE F E) × (Fin n → Fin n → AfE F E)) :=
    hφ.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact ht)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨u1, hu1, hu1s⟩ := pi_small (0 : Fin n → AfE F E) u hu
  obtain ⟨u2, hu2, hu2s⟩ := pi_small (0 : AfE F E) u1 hu1
  obtain ⟨v1, hv1, hv1s⟩ := pi_small (0 : Fin n → AfE F E) v hv
  obtain ⟨v2, hv2, hv2s⟩ := pi_small (0 : AfE F E) v1 hv1
  obtain ⟨m₀, hm₀, hm⟩ := exists_nsmul_intAf (F := F) (E := E) (u2 ∩ v2) (Filter.inter_mem hu2 hv2)
  refine ⟨m₀, hm₀, fun m hdvd hm0 k hk hk' => hts ?_⟩
  have ent : ∀ g : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) g → ∀ i j,
      (g : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ u2 ∩ v2 := by
    intro g hg i j
    obtain ⟨y, hy, e⟩ := mem_of_congOne_entry hdvd hm0 _ (hg i j)
    rw [e]
    exact hm y hy
  have e : Units.embedProduct _ k = φ (fun i j => (k : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j,
      fun i j => ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    refine Prod.ext ?_ ?_
    · show (k : Matrix (Fin n) (Fin n) (AfE F E)) = _
      ext i j
      simp [φ]
    · show MulOpposite.op ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = _
      congr 1
      ext i j
      simp
  show Units.embedProduct _ k ∈ t
  rw [e]
  exact huv ⟨hu1s _ fun i => hu2s _ fun j => (ent k hk i j).1, hv1s _ fun i => hv2s _ fun j => (ent _ hk' i j).2⟩

end Main

end GlobalTheory.Mem.ColAd.Nbhd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


open Classical in
noncomputable def wtPre (P : Pre) (j : ℕ) (aP : Tau P.R → Fin (P.R.sigW j).1 → ℕ) (aM : Tau P.R → Fin (P.R.sigW j).2 → ℕ)
    (x : (P.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : Tau P.R, ((if x.1 = P.host.emb t.1 then Formalism.L2.Pj.ext0 (aP t) x.2 else 0) +
    if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (P.host.emb t.1) then Formalism.L2.Pj.ext0 (aM t) x.2 else 0)

theorem cusp_type_congr {P₁ P₂ : Pre} (hP : P₂ = P₁)
    {H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₁.host.E} {H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₂.host.E}
    {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁} {c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {Xo₁ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₁ j) l₁} {Xo₂ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₂ j) l₂}
    {U₁ : ∀ j (σ : c₁.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₁ j) c₁ σ P₁.R.r}
    {U₂ : ∀ j (σ : c₂.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₂ j) c₂ σ P₂.R.r}
    {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    {aP₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).1 → ℕ} {aP₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).1 → ℕ}
    {aM₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).2 → ℕ} {aM₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).2 → ℕ}
    {n₁ n₂ : ℕ} (hn : n₂ = n₁)
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hDw : HEq Dw₂ Dw₁) (hXo : HEq Xo₂ Xo₁) (hU : HEq U₂ U₁)
    (haP : HEq aP₂ aP₁) (haM : HEq aM₂ aM₁) :
    ↥(Formalism.L2.Pj.cusp (Xo₂ j₂) c₂ (U₂ j₂) (wtPre P₂ j₂ aP₂ aM₂) n₂) =
      ↥(Formalism.L2.Pj.cusp (Xo₁ j₁) c₁ (U₁ j₁) (wtPre P₁ j₁ aP₁ aM₁) n₁) := by
  subst hP hj hn
  cases hH; cases hl; cases hc; cases hDw; cases hXo; cases hU; cases haP; cases haM
  rfl

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem Ext.cuspA_type_eq : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX i₁ i₂ hi
  have hk := hX.κ i₁ i₂ hi
  exact (cusp_type_congr hE.left (congrArg (fun x ↦ x + 1) hi) hk.right.right hX.H hX.l hX.c hX.Dw hX.Xo hX.U hk.left hk.right.left)

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl

theorem exists_below_between : ∀ (D₁ D₂ D₃ : Formalism.BasicNotions.D7), Set.range D₂.what₂.embLL ⊆ Set.range D₃.what₂.embLL → ∀ (v₁ : D₁.what₂.places.Pl) (v₃ : D₃.what₂.places.Pl), GlobalTheory.Mem.Top.Bl.Below D₁ D₃ v₁ v₃ → ∃ v₂ : D₂.what₂.places.Pl, GlobalTheory.Mem.Top.Bl.Below D₁ D₂ v₁ v₂ ∧ GlobalTheory.Mem.Top.Bl.Below D₂ D₃ v₂ v₃ := by
  intro D₁ D₂ D₃ hR v₁ v₃ h13

  have hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange := fun x => by
    obtain ⟨y, hy⟩ := hR ⟨x, rfl⟩
    exact ⟨y, hy⟩
  let ι : D₂.what₂.LL →+* D₃.what₂.LL :=
    (D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)
  have hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x := fun x => by
    have := (D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩
    exact congrArg Subtype.val this
  let ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL := RingOfIntegers.mapRingHom ι
  have hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL) := fun x => rfl
  set Q := (D₃.plEq v₃).asIdeal with hQ
  let P : Ideal (𝓞 D₂.what₂.LL) := Q.comap ιO
  have hPprime : P.IsPrime := Ideal.comap_isPrime ιO Q
  have hQne : Q ≠ ⊥ := (D₃.plEq v₃).ne_bot
  have hn : Ideal.absNorm Q ≠ 0 := by
    intro h; exact hQne (Ideal.absNorm_eq_zero_iff.mp h)
  have hPne : P ≠ ⊥ := by
    intro h
    have hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P := by
      show ιO _ ∈ Q
      rw [map_natCast]; exact Ideal.absNorm_mem Q
    rw [h, Ideal.mem_bot] at hin
    exact hn (by exact_mod_cast hin)
  refine ⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩
  · intro x₁ x₂ hx
    rw [Equiv.apply_symm_apply]
    show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q
    exact h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)
  · intro x₂ x₃ hx
    rw [Equiv.apply_symm_apply]
    show ιO x₂ ∈ Q ↔ x₃ ∈ Q
    have : ιO x₂ = x₃ := by
      apply Subtype.ext
      apply D₃.what₂.embLL.injective
      show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _
      rw [hι]; exact hx
    rw [this]

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
section
open NumberField IsDedekindDomain

namespace GlobalTheory.PrimeBelow

theorem exists_prime_below {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] (σ : K →+* ℂ) (τ : L →+* ℂ)
    (h : Set.range σ ⊆ Set.range τ) (P : HeightOneSpectrum (𝓞 L)) :
    ∃ p : HeightOneSpectrum (𝓞 K), ∀ (x : 𝓞 K) (y : 𝓞 L), σ (x : K) = τ (y : L) → (x ∈ p.asIdeal ↔ y ∈ P.asIdeal) := by
  classical

  have hmem : ∀ x : K, σ x ∈ τ.range := fun x => RingHom.mem_range.2 (h ⟨x, rfl⟩)
  obtain ⟨ι, hι⟩ : ∃ ι : K →+* L, ∀ x, τ (ι x) = σ x := by
    let e := RingEquiv.ofBijective τ.rangeRestrict
      ⟨fun a b hab => τ.injective (congrArg Subtype.val hab), τ.rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (σ.codRestrict τ.range hmem), fun x => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨σ x, hmem x⟩)
  let φ : 𝓞 K →+* 𝓞 L := RingOfIntegers.mapRingHom ι

  have hne : P.asIdeal.comap φ ≠ ⊥ := by
    have hZ : P.asIdeal.comap (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
      fun hb => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
    intro hbot
    have hmK : ((m : 𝓞 K)) ∈ P.asIdeal.comap φ := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hm
    rw [hbot, Ideal.mem_bot] at hmK
    have : ((m : K)) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hmK
      simpa using this
    exact hm0 (by exact_mod_cast this)
  have := P.isPrime
  refine ⟨⟨P.asIdeal.comap φ, Ideal.comap_isPrime φ P.asIdeal, hne⟩, fun x y hxy => ?_⟩
  have hxy' : φ x = y := by
    apply RingOfIntegers.ext
    apply τ.injective
    rw [RingOfIntegers.mapRingHom_apply, hι, hxy]
  show x ∈ P.asIdeal.comap φ ↔ y ∈ P.asIdeal
  rw [Ideal.mem_comap, hxy']

theorem exists_below : ∀ (D D' : Formalism.BasicNotions.D7), Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D)) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D) → ℂ) ⊆ Set.range (⇑(Formalism.BasicNotions.Rows.Data.embLL (Formalism.BasicNotions.D7.what₂ D')) : Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D') → ℂ) → ∀ (v' : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D'))), ∃ (v : Formalism.BasicNotions.Rows.Places.Pl (Formalism.BasicNotions.Rows.Data.places (Formalism.BasicNotions.D7.what₂ D))), GlobalTheory.Mem.Top.Bl.Below D D' v v' := by
  intro D D' h v'
  obtain ⟨p, hp⟩ := exists_prime_below _ _ h (D'.plEq v')
  refine ⟨D.plEq.symm p, fun x x' hx => ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hp x x' hx

end GlobalTheory.PrimeBelow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepGroupElement_of_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level | exact GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedCoefficientFieldInComplex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

def SeedW (K : Ctx) (P : Pre) (f : Fr P) (F F₀ : IntermediateField ℚ ℂ) (px : PreX P) (S : Set ℕ) (L : IntermediateField ℚ ℂ) :
    Prop :=
  ∃ (B₀ : Base) (f₀ : Fr B₀.toPre) (T₀ : TwDat B₀) (w₀ : ColW B₀ f₀ T₀) (Z₀ : w₀.Lt) (hX₀ : B₀.fields.Ok) (Wt₀ : Set B₀.places.Pl)
    (z₀ : Dat (w₀.st Z₀) w₀.I hX₀ T₀ Wt₀), B₀.toPre = P ∧ HEq f₀ f ∧ B₀.KsC = F ∧ B₀.fixedCoefficientFieldInComplex = F₀ ∧ HEq w₀.px px ∧
      Pinned K B₀ f₀ T₀ w₀ ∧ GrpTrue Z₀.N f₀ ∧ GrpAt (w₀.st Z₀) w₀.I ∧ Fine z₀ ∧ HoldsL z₀.R z₀.F ∧
      (∀ v ∈ z₀.W1 (fun _ _ => 0), B₀.places.resChar v ∈ S) ∧ B₀.LLC ≤ L

theorem SeedW.mono {K : Ctx} {P : Pre} {f : Fr P} {F F₀ : IntermediateField ℚ ℂ} {px : PreX P} {S S' : Set ℕ}
    {L L' : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ px S L) (hS : S ⊆ S') (hL : L ≤ L') : SeedW K P f F F₀ px S' L' := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => hS (a11 v hv), a12.trans hL⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChainsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_form_true_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = ((I.rec7 l Z).chTw u μ).Kmap i c c' (evC O u μ i v) → ∀ J, prTC Pl O Bs u μ w i c' v' J = unC Pl O Bs u μ w i c c' * prSC Pl O Bs u μ w i c v (KM.applyAt0 ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) ((I.rec7 l Z).what₂.places.resChar w) (thAtW Pl O Bs u μ w i c c') (KM.Gxz ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i) J)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | exact GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEnt_kform_true <;> assumption)
end

