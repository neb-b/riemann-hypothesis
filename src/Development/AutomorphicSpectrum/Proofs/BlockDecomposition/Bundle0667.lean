module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpen
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne_zero_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {V K : Subgroup H}
    (hV : IsOpen (V : Set H)) (hK : IsCompact (K : Set H)) : V.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ V.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hV.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem finH_mul (x y : Hf E a b) : finH (x * y) = finH x * finH y :=
  Prod.ext (map_mul (finGL E a) _ _) (map_mul (finGL E b) _ _)

theorem finH_one : finH (1 : Hf E a b) = 1 :=
  Prod.ext (map_one (finGL E a)) (map_one (finGL E b))

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b)
    (he₁ : ∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1), finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2))
    (he₂ : ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
      finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2))
    (i : Slot S) (G : H E a b → ℂ) (z : H E a b) :
    actS φ₁ φ₂ i G z = hint (K2 a b i.pl) fun m => sf φ₁ φ₂ i m * G (z * finH (e i m)) := by
  rcases i with w | w
  · change hint (K2 a b w.1) (fun m => φ₁ w.1 m * pairRt a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₁ w.1 m * G (z * finH (e (.inl w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₁]
    rfl
  · change hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₂ w.1 m * G (z * finH (e (.inr w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₂]
    rfl

theorem finActOf : FinActOf := by
  intro hInt hSl hConv _ E _ _ _ B S hS φ₁ φ₂ h₁ h₂ G hG l hl hfix x
  haveI := B.hν
  haveI := B.hν'
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hmul, hcont, hsep, -, hev, hmem, -⟩ := hSl E B.a B.b S hS
  obtain ⟨e, hec, hpe, hpe', he₁, he₂⟩ := _root_.GlobalTheory.CompanionTheory.FinActS.exists_factorEmb (E := E) B.a B.b hS
  obtain ⟨U₀, hU₀, hlev⟩ := hG
  obtain ⟨-, hc⟩ := hConv E B S hS
  obtain ⟨hcs, ⟨U₁, hU₁, hinv⟩, -⟩ := hc φ₁ φ₂ h₁ h₂
  obtain ⟨L, hLo, hLe, hLi, hLc, hLu⟩ := GlobalTheory.T.position_level_subgroups_exist (S := S) h₁ h₂
  let p : ∀ i : Slot S, Hf E B.a B.b →* GLw B.a i.pl × GLw B.b i.pl := fun i => MonoidHom.mk' (i.cp B.a B.b) (hmul i)
  let K : Subgroup (Hf E B.a B.b) := (Kf E B.a).prod (Kf E B.b)
  have hKo : IsOpen (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  have hKc : IsCompact (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf
  have hKHo : ∀ i : Slot S, IsOpen (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isOpen_K i.pl
  have hKHc : ∀ i : Slot S, IsCompact (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isCompact_K i.pl
  obtain ⟨V₀, hV₀o, hV₀K, hV₀e, hV₀U⟩ := _root_.GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open p e K (fun i => K2 B.a B.b i.pl) hcont hec hpe hpe' hsep hmem hKc hKHo U₀ hU₀
  let V : ∀ i : Slot S, Subgroup (GLw B.a i.pl × GLw B.b i.pl) := fun i => V₀ i ⊓ L i
  have hVo : ∀ i, IsOpen (V i : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i => by
    simp only [V, Subgroup.coe_inf]
    exact (hV₀o i).inter (hLo i)
  let g : Hf E B.a B.b → ℂ := fun h => G (x * finH h)
  have hact := actS_eq φ₁ φ₂ e he₁ he₂
  have hcore := _root_.GlobalTheory.CompanionTheory.FinActCore.hint_prod_eq_foldr p e K (fun i => K2 B.a B.b i.pl) V (sf φ₁ φ₂) hpe hpe' hsep hev hmem
    (fun i => inf_le_left.trans (hV₀K i)) (fun i => relIndex_ne_zero_of_open (hVo i) (hKHc i))
    (by
      filter_upwards [hV₀e, hLe, hLu] with i a₁ a₂ a₃
      exact ⟨by simp only [V, a₁, a₂, inf_idem], a₃⟩)
    (fun i u hu y => hLi i u hu.2 y)
    (fun i => GlobalTheory.TwTrLin.finite_out_support (hVo i) (hLc i))
    g
    (fun u hu y => by
      have hu₀ : u ∈ U₀ := hV₀U u fun i => (hu i).1
      simp only [g]
      rw [finH_mul, ← mul_assoc]
      exact hlev u hu₀ _)
    l hl
    (fun i hi => funext fun y => by
      have h1 := hact i G (x * finH y)
      rw [hfix i hi] at h1
      simp only [g, finH_mul, ← mul_assoc]
      exact h1.symm)
  have hfold : ∀ (l' : List (Slot S)) (y : Hf E B.a B.b),
      l'.foldr (fun i g' x => hint (K2 B.a B.b i.pl) fun m => sf φ₁ φ₂ i m * g' (x * e i m)) g y =
        l'.foldr (fun i g' => actS φ₁ φ₂ i g') G (x * finH y) := by
    intro l'
    induction l' with
    | nil => intro y; rfl
    | cons i l' ih =>
      intro y
      simp only [List.foldr_cons]
      rw [hact]
      refine congrArg _ (funext fun m => ?_)
      rw [ih, finH_mul, mul_assoc]
  have hint₁ := hInt (Hf E B.a B.b) B.ν K (U₀ ⊓ U₁) (fun h => finFn S φ₁ φ₂ h * g h) hKo hKc
    (by rw [Subgroup.coe_inf]; exact hU₀.inter hU₁) hcs.mul_right
    (fun u hu y => by
      have e1 := (hinv u hu.2 y).2
      simp only [g]
      rw [e1, finH_mul, ← mul_assoc, hlev u hu.1])
    inferInstance
  have hF : (fun h => finFn S φ₁ φ₂ h * g h) = fun h => (∏ᶠ i : Slot S, sf φ₁ φ₂ i (p i h)) * g h :=
    funext fun h => by rw [GlobalTheory.T.finite_test_function_product h₁ h₂]; rfl
  have hfin := hfold l 1
  rw [finH_one, mul_one] at hfin
  rw [← hfin, ← hcore, ← hF]
  exact hint₁

end GlobalTheory.CompanionTheory.FinActS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleRev

theorem exists_isSocle_prodIrr_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k →
    LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N),
    IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  intro k _ _ _ _ hA hJ hI hC h N Γ y hd hR hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order Γ
  have hR' : IsRevOrdered (Γ ∘ σ) := _root_.GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon _ hσ
  have hd' : ∑ a, (y (σ a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp σ (fun a => (y a).1)
  obtain ⟨e₁⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA hC Γ σ y hd hd' hR hR' hL
  have hL' : ∀ i, IsLSeg ((Γ ∘ σ) i) ((y ∘ σ) i).rep := fun i => hL (σ i)
  obtain ⟨g, z, hz, ⟨e₂⟩, hjm⟩ := GlobalTheory.T.canonical_product_equiv_multiplicity_one hA hJ hI (Γ ∘ σ) (y ∘ σ) hd' hσ hL'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.socle_of_multiplicity_one hA z hz hjm
  exact ⟨τ, hτ.of_equiv (Representation.Equiv.refl _) (e₁.trans e₂).symm⟩

end GlobalTheory.CompanionTheory.SocleRev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSum
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem dsum_stronglyMeasurable : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  intro D ρ p ψ hψ b₀ Φ hΦ hs
  haveI := (_root_.GlobalTheory.CompanionTheory.FJE.countable_mat_cosets D ρ p).1
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, hc⟩ := _root_.GlobalTheory.CompanionTheory.FJE.chv_facts ψ hψ b₀
  have hterm : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, Measurable fun v : Mx D ρ p × Mx D ρ p =>
      GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.2 (GlobalTheory.CompanionTheory.FJE.rt ξ) * Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + v.1) := by
    intro ξ
    have h1 : Measurable fun y : Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ y (GlobalTheory.CompanionTheory.FJE.rt ξ) :=
      (hc.comp (continuous_id.prodMk continuous_const)).measurable
    have h2 : Measurable fun y : Mx D ρ p => Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y) :=
      hΦ.measurable.comp (continuous_const_add (GlobalTheory.CompanionTheory.FJE.rt ξ)).measurable
    exact (h1.comp measurable_snd).mul (h2.comp measurable_fst)
  exact (Measurable.tsum hterm).stronglyMeasurable

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestTContinuousHasCompactSupport
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC

variable {F : Type} [Field F] [NumberField F]

def boxW (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v) :=
  {x | (v ∈ S → x ∈ U v) ∧ (v ∉ S → x ∈ v.adicCompletionIntegers F)}

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_integer _

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact isCompact_iff_compactSpace.2 inferInstance

theorem isOpen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsOpen (U v)) :
    IsOpen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  have h1 : IsOpen {y : Af F | ∀ v ∈ S, y v ∈ U v} := by
    have : {y : Af F | ∀ v ∈ S, y v ∈ U v} = ⋂ v ∈ S, (fun y : Af F => y v) ⁻¹' U v := by
      ext y; simp
    rw [this]
    exact isOpen_biInter_finset fun v _ => (hU v).preimage (RestrictedProduct.continuous_eval v)
  have h2 : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_integers v)
  exact h1.inter h2

theorem isCompact_boxW (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v))
    (v : HeightOneSpectrum (𝓞 F)) : IsCompact (boxW S U v) := by
  by_cases hv : v ∈ S
  · have : boxW S U v = U v := by
      ext x; simp [boxW, hv]
    rw [this]; exact hU v
  · have : boxW S U v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [boxW, hv]
    rw [this]; exact isCompact_integers v

theorem isCompact_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v)) :
    IsCompact (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  haveI : ∀ v, CompactSpace (boxW S U v) := fun v => isCompact_iff_compactSpace.1 (isCompact_boxW S U hU v)
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal ((S : Set _)ᶜ) :=
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let gP : (∀ v, boxW S U v) → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal ((S : Set _)ᶜ)) :=
    fun x => ⟨fun v => (x v).1, Filter.eventually_principal.2 fun v hv => (x v).2.2 (by simpa using hv)⟩
  have hgP : Continuous gP :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff.2
      (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  let g : (∀ v, boxW S U v) → Af F := fun x => RestrictedProduct.inclusion _ _ hle (gP x)
  have hg : Continuous g := (RestrictedProduct.continuous_inclusion hle).comp hgP
  have hr : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U = Set.range g := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => ⟨y v, fun hv => h1 v hv, fun hv => h2 v hv⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun v hv => (x v).2.1 hv, fun v hv => (x v).2.2 hv⟩
  rw [hr]
  exact isCompact_range hg

theorem isClopen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v) ∧ IsOpen (U v)) :
    IsClopen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) :=
  ⟨(isCompact_boxA S U fun v => (hU v).1).isClosed, isOpen_boxA S U fun v => (hU v).2⟩

theorem testT_continuous_hasCompactSupport : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
    Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) →
    Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧
      HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  intro F _ _ ρ S U hρ hρc hU
  have hB := isClopen_boxA S U hU
  have hBc := isCompact_boxA S U fun v => (hU v).1
  have hfst : Continuous (fun y : AF F => fstA F y) := continuous_fst
  have hsnd : Continuous (fun y : AF F => sndA F y) := continuous_snd
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    refine (Complex.continuous_ofReal.comp (hρ.comp hfst)).mul ?_
    exact (IsClopen.continuous_indicator hB continuous_const).comp hsnd
  · have hK : IsCompact ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F)) :=
      hρc.isCompact.prod hBc
    refine HasCompactSupport.intro (K := ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F))) hK ?_
    intro y hy
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    by_cases h1 : sndA F y ∈ GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U
    · have h2 : ρ (fstA F y) = 0 := by
        by_contra h3
        exact hy ⟨subset_tsupport ρ h3, h1⟩
      simp [h2]
    · simp [Set.indicator_of_notMem h1]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC
end
end

