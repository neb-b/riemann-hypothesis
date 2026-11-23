module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddSingle
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureOpenNonemptyNeZeroStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_open_nonempty_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    ((muD k t) E).toReal ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagAvg

theorem avg_conj {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (f : G → ℂ) (hl : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g)
    (g : G) :
    avg (fun k : K => f ((k : G)⁻¹ * g * k)) = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * g * x) := by
  set S : Subgroup K := K'.subgroupOf K with hSdef
  set u : K → ℂ := fun k => f ((k : G)⁻¹ * g * k) with hu
  have hS : S ≤ rStab u := by
    intro s hs k
    have hs' : (s : G) ∈ K' := Subgroup.mem_subgroupOf.1 hs
    show f (((k * s : K) : G)⁻¹ * g * ((k * s : K) : G)) = f ((k : G)⁻¹ * g * k)
    have e : ((k * s : K) : G)⁻¹ * g * ((k * s : K) : G) = (s : G)⁻¹ * ((k : G)⁻¹ * g * k) * s := by
      simp only [Subgroup.coe_mul]; group
    rw [e, (hl _ hs' _).2, (hl _ (K'.inv_mem hs') _).1]
  let φ : {x // x ∈ X} → K ⧸ S := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ S)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := by
        have h2 := QuotientGroup.eq.1 hxy
        exact Subgroup.mem_subgroupOf.1 h2
      have hy := hX y.1 (hXK _ y.2)
      exact Subtype.ext (hy.unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  let e := Equiv.ofBijective φ hφ
  have hindex : S.index = X.card := by
    show Nat.card (K ⧸ S) = _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : S.index ≠ 0 := by
    rw [hindex]
    obtain ⟨x, ⟨hxX, -⟩, -⟩ := hX 1 K.one_mem
    exact (Finset.card_pos.2 ⟨x, hxX⟩).ne'
  rw [GlobalTheory.CompanionTheory.AvgLevel.avg_eq_level S u hS hne, hindex]
  congr 1
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨x.1, hXK _ x.2⟩ : K)
  show u (φ x).out = u ⟨x.1, hXK _ x.2⟩
  have hφx : (φ x).out = (⟨x.1, hXK _ x.2⟩ : K) * s := hs
  rw [hφx]
  exact hS s.2 _

theorem hint_const_mul_sum {H ι : Type} [Group H] (A L : Subgroup H) (hLA : L ≤ A) (hfin : L.relIndex A ≠ 0)
    (s : Finset ι) (v : ι → H → ℂ) (c : ℂ) (hst : ∀ i ∈ s, L ≤ rStab (v i))
    (hsupp : ∀ i ∈ s, (Function.support fun q : H ⧸ L => v i q.out).Finite) :
    hint A (fun z => c * ∑ i ∈ s, v i z) = c * ∑ i ∈ s, hint A (v i) := by
  have hL : L ≤ rStab (fun z => c * ∑ i ∈ s, v i z) := by
    intro l hl z
    show c * ∑ i ∈ s, v i (z * l) = c * ∑ i ∈ s, v i z
    congr 1
    exact Finset.sum_congr rfl fun i hi => hst i hi hl z
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L _ hLA hL hfin,
    Finset.sum_congr rfl fun i hi => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L (v i) hLA (hst i hi) hfin,
    ← Finset.mul_sum]
  have h1 : ∑ᶠ q : H ⧸ L, c * ∑ i ∈ s, v i q.out = c * ∑ i ∈ s, ∑ᶠ q : H ⧸ L, v i q.out := by
    simp only [Finset.mul_sum]
    rw [finsum_sum_comm s (fun (q : H ⧸ L) i => c * v i q.out) fun i hi =>
      (hsupp i hi).subset fun q hq => right_ne_zero_of_mul hq]
    exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  rw [h1]
  ring

theorem support_finite {G H : Type} [Group G] [Group H] (L : Subgroup H) (K' : Subgroup G) (θ : H → G)
    (hθ : ∀ z z', (θ z)⁻¹ * θ z' ∈ K' → z⁻¹ * z' ∈ L) (f : G → ℂ) (hr : ∀ u ∈ K', ∀ g, f (g * u) = f g)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    (Function.support fun q : H ⧸ L => f (θ q.out)).Finite := by
  refine Set.Finite.of_finite_image (f := fun q : H ⧸ L => ((θ q.out : G) : G ⧸ K')) (hfin.subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (θ q.out)
    show f ((θ q.out : G) : G ⧸ K').out ≠ 0
    rw [hs, hr _ s.2]
    exact hq
  · intro q _ q' _ hqq
    have h2 : ((q.out : H) : H ⧸ L) = q'.out := QuotientGroup.eq.2 (hθ _ _ (QuotientGroup.eq.1 hqq))
    simpa using h2

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (ho : IsOpen (K' : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) : {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun i : G ⧸ K' => {g : G | i.out⁻¹ * g ∈ K'})
    (fun i => ho.preimage (continuous_const.mul continuous_id)) fun g _ =>
      Set.mem_iUnion.2 ⟨(g : G ⧸ K'), QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ K'))⟩
  refine t.finite_toSet.subset fun q hq => ?_
  obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have h1 : ((i.out : G) : G ⧸ K') = q.out := QuotientGroup.eq.2 hqi
  have h2 : i = q := by simpa using h1
  exact h2 ▸ hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_toAdd_mul {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (Z l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd (Z * l)) =
      blk h w m (Multiplicative.toAdd Z) * blk h w 1 (Multiplicative.toAdd l) := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp [add_comm]

theorem ct_eq_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX f hf m
  have hbi : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g := fun u hu g =>
    ⟨by simpa using hf.2.2.2 u hu 1 K'.one_mem g, by simpa using hf.2.2.2 1 K'.one_mem u hu g⟩
  have hcos := finite_cosets K' hopen f hf.2.2.1
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hopen hle
  set L := (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) with hLdef
  have hmem : ∀ Y, Y ∈ L ↔ blk h w 1 (Multiplicative.toAdd Y) ∈ K' := fun Y => Iff.rfl
  have hstep : (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Z) * k)) =
      fun Z => ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) :=
    funext fun Z => avg_conj _ K' X hXK hX f hbi _
  have hst : ∀ x ∈ X, L ≤ rStab (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) := by
    intro x hx l hl Z
    show f (x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x) = f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)
    have hU : x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x ∈ K' := by
      simpa using hnorm x⁻¹ ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hXK x hx)) _ ((hmem l).1 hl)
    have e : x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x =
        (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) * (x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x) := by
      rw [blk_toAdd_mul]; group
    rw [e]
    exact (hbi _ hU _).2
  have hsupp : ∀ x ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd q.out) * x)).Finite := by
    intro x hx
    refine support_finite L K' (fun Z => x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) ?_ f
      (fun u hu g => (hbi u hu g).2) hcos
    intro z z' hz
    rw [hmem]
    have hb : blk h w m (Multiplicative.toAdd z') =
        blk h w m (Multiplicative.toAdd z) * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by
      rw [← blk_toAdd_mul, mul_inv_cancel_left]
    have e : (x⁻¹ * blk h w m (Multiplicative.toAdd z) * x)⁻¹ * (x⁻¹ * blk h w m (Multiplicative.toAdd z') * x) =
        x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x := by
      rw [hb]; group
    have hz' : x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x ∈ K' := e ▸ hz
    have := hnorm x (hXK x hx) _ hz'
    have e2 : x * (x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x) * x⁻¹ =
        blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by group
    rwa [e2] at this
  simp only [ct, phi3]
  rw [hstep, hint_const_mul_sum (intMat a b w) L hLA hfin X
    (fun x Z => f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) _ hst hsupp, ← Finset.mul_sum]
  ring

end GlobalTheory.CompanionTheory.DiagAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalksStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplane_cut_good_stalks : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec), GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec) → Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | exact GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisTer
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨_root_.GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac k N h d hd J hJo hJc hJf hpos V π hπ.1,
    _root_.GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective k N h d hd J hJo hJc hJf hpos V π hπ,
    _root_.GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOneStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_derivative_at_one : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∀ a b : Fin n, lev b ≤ lev a → (e1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (lam a : ℂ) else 0) ∧ (f1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) else 0) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FDer.fder | exact GlobalTheory.CompanionTheory.ModelS.FDer.fder | (intros; apply GlobalTheory.CompanionTheory.ModelS.FDer.fder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFinite
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open GlobalTheory.CompanionTheory.ModelS.FFin in
theorem GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ)
    (hlev : IsLev lam lev) (F : GlobalTheory.CompanionTheory.ModelS.SmF n) (hF : F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev) :
    ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧
      ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  obtain ⟨m, p, hp⟩ := fRaw_factor lam hl lev hlev
  set e := GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev) with he
  have hfin : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree) := inferInstance
  refine ⟨(MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree).map (wfL e m), inferInstance,
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩, ?_⟩
  · apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · show wf e m p g = F.1 g
      rw [hF, hp g hg, wf, Set.indicator_of_mem hg]
    · show wf e m p g = F.1 g
      rw [wf, Set.indicator_of_notMem hg, F.2.2 g hg]
  · rintro a b _ ⟨q, hq, rfl⟩
    refine ⟨(if a = b then (m : ℂ) else 0) • q + Tp a b q,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hq) (Tp_mem a b _ hq), ?_⟩
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · rw [Kf_wf e m q (wfL e m q) rfl a b hg]
      show wf e m _ g = _
      rw [wf, Set.indicator_of_mem hg, evalPoints_add, evalEmbedding_smul]
    · show wf e m _ g = _
      rw [wf, Set.indicator_of_notMem hg, (GlobalTheory.CompanionTheory.ModelS.Kf a b (wfL e m q)).2.2 g hg]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedEmbeddingsCount
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.IntegerCount

theorem card_bounded_conjugates_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
    {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R}.Finite ∧
    (Set.ncard {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} : ℝ) ≤ C * R ^ Module.finrank ℚ E := by
  intro E _ _
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis ι ℤ (𝓞 E) := RingOfIntegers.basis E
  let B := canonicalEmbedding.latticeBasis E

  let L : ι → (((E →+* ℂ) → ℂ) →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (B.coord i)
  let C₀ : ℝ := ∑ i, ‖L i‖
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoord : ∀ (β : 𝓞 E) (i : ι), L i (canonicalEmbedding E (β : E)) = ((b.repr β i : ℤ) : ℂ) := by
    intro β i
    have hx : canonicalEmbedding E (β : E) = ∑ j, ((b.repr β j : ℤ) : ℂ) • B j := by
      have h0 : (β : E) = ∑ j, ((b.repr β j : ℤ) : E) * ((b j : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr β]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, zsmul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h0, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext τ
      simp [B, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    change B.coord i _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hbound : ∀ (R : ℝ), 1 ≤ R → ∀ β : 𝓞 E, (∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R) →
      ∀ i, |((b.repr β i : ℤ) : ℝ)| ≤ C₀ * R := by
    intro R hR β hβ i
    have hx : ‖canonicalEmbedding E (β : E)‖ ≤ R :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun τ => by simpa using hβ τ
    have h1 : ‖L i (canonicalEmbedding E (β : E))‖ ≤ ‖L i‖ * R :=
      ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    rw [hcoord, Complex.norm_intCast] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    exact Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank E]
    exact (Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)).symm
  refine ⟨(2 * C₀ + 1) ^ Module.finrank ℚ E, by positivity, fun R hR => ?_⟩
  set S : Set (𝓞 E) := {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} with hS
  let N : ℤ := ⌊C₀ * R⌋
  have hN0 : 0 ≤ N := Int.floor_nonneg.2 (by nlinarith)
  let box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N
  let f : 𝓞 E → (ι → ℤ) := fun β i => b.repr β i
  have hf : Function.Injective f := by
    intro x y hxy
    apply b.repr.injective
    ext i
    exact congrFun hxy i
  have hmaps : Set.MapsTo f S (box : Set (ι → ℤ)) := by
    intro β hβ
    simp only [box, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := abs_le.1 (hbound R hR β hβ i)
    constructor
    · have h2 : -(b.repr β i) ≤ N := Int.le_floor.2 (by push_cast; linarith [h.1])
      change -N ≤ b.repr β i
      omega
    · exact Int.le_floor.2 h.2
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn box.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle : S.ncard ≤ box.card := by
    have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn box.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hboxcard : (box.card : ℝ) = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := by
    have h1 : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    have h2 : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      exact_mod_cast h1
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard]
    push_cast
    rw [h2]
  have hNle : (N : ℝ) ≤ C₀ * R := Int.floor_le _
  calc (S.ncard : ℝ) ≤ box.card := by exact_mod_cast hle
    _ = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := hboxcard
    _ ≤ ((2 * C₀ + 1) * R) ^ Module.finrank ℚ E := by
        have hN0' : (0 : ℝ) ≤ N := by exact_mod_cast hN0
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = (2 * C₀ + 1) ^ Module.finrank ℚ E * R ^ Module.finrank ℚ E := mul_pow _ _ _

end GlobalTheory.CompanionTheory.IntegerCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) : HermE D r :=
  ⟨(a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a, by
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have hβ := β.2
    have hm : ∀ (X Y : Matrix (Fin r) (Fin r) D.host.E),
        (X * Y).map (D.sp.cm.sig : D.host.E → D.host.E) =
          X.map (D.sp.cm.sig : D.host.E → D.host.E) * Y.map (D.sp.cm.sig : D.host.E → D.host.E) :=
      fun X Y => Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [hm, hm, Matrix.transpose_mul, Matrix.transpose_mul, hβ]
    have h2 : ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = a := by
      ext i j; simp [hσ]
    rw [h2, Matrix.mul_assoc]⟩

def IsBlockNF {r : ℕ} (t : ℕ) (β : HermE D r) : Prop :=
  ∃ h : t < r, (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β.1 i j = 0) ∧
    (β.1.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRank

theorem isCompactOperator_repOp_Rcusp_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E 0 → ℂ) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  have := SpecModel.finiteDimensional_zero μ
  have : FiniteDimensional ℂ (L2cusp μ) := inferInstance
  have : ProperSpace (L2cusp μ) := FiniteDimensional.proper ℂ _
  exact isCompactOperator_of_locallyCompactSpace_rng _

end GlobalTheory.CompanionTheory.CuspRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_standard_maximal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @GlobalTheory.CompanionTheory.StdK.isCompact_K | exact GlobalTheory.CompanionTheory.StdK.isCompact_K | (intros; apply GlobalTheory.CompanionTheory.StdK.isCompact_K <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizerStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariant_cup_uniformizer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | exact GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | (intros; apply GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top <;> assumption)
end

