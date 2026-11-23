module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesRationalDecompositionsOverLoca
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  have hi : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
    obtain ⟨η, hη, h0, h⟩ := exists_idem p
    have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
      refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
      · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        exact TensorProduct.zero_tmul _ _
      · refine Ideal.mem_iInf.2 fun w => ?_
        change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
        rw [h0 w.1 w.2, TensorProduct.zero_tmul]
    have := pr_int p (hU.1 _ hm).2.2
    rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this
  have h0 : D.host.xi0 ≠ 0 := fun h => by
    have := GlobalTheory.MixModel.HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
    rw [h, map_zero, zero_mul] at this
    have h2 := congrArg p.pr this
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have a := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral p hU)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D D.host.xi0)) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

theorem val_star_xi (p : SplitPt D k) (hU : p.UnitAA) : valuation k (p.pr (incA D (star D.host.xi0))) = 1 := by
  rw [Brg.star_purely_imaginary_eq_neg, map_neg, map_neg, Valuation.map_neg, val_xi p hU]

theorem val_nat (p : SplitPt D k) {PP : Pl D.host.E} (hI : Formalism.L2.NTheta.IsIdemAt p.e PP) (n : ℕ)
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : valuation k (p.pr (incA D (n : D.host.E))) = 1 := by
  have hx : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hn (h ▸ PP.asIdeal.zero_mem)
  have h1 := (hI.2 _ hx).not.1 hn
  rw [not_not] at h1
  have hcast : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := by simp
  rw [hcast] at h1
  have hi : p.pr (incA D (n : D.host.E)⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact h1
  have hn0 : (n : D.host.E) ≠ 0 := by
    intro h; apply hx; exact_mod_cast (by rw [hcast]; exact h : (((n : ℕ) : 𝓞 D.host.E) : D.host.E) = 0)
  have a : valuation k (p.pr (incA D (n : D.host.E))) ≤ 1 := by
    rw [map_natCast, map_natCast]
    exact (Valuation.mem_integer_iff _ _).1 (natCast_mem _ n)
  have b := (Valuation.mem_integer_iff _ _).1 hi
  have ab : valuation k (p.pr (incA D (n : D.host.E))) * valuation k (p.pr (incA D (n : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hn0, map_one, map_one, map_one]
  exact le_antisymm a (by calc (1 : ValueGroupWithZero k) = _ := ab.symm
      _ ≤ valuation k (p.pr (incA D (n : D.host.E))) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _)

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tau_norm {a : XGeo D} (y : YRat a) {lam : D.host.E} (hT : y.Tau lam) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    star lam * (lam * (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ)) =
      -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
  obtain ⟨h1, h2⟩ := hT j h
  have h3 := congrArg (fun A => star a.ζ₀ ⬝ᵥ A *ᵥ a.ζ₀) h1
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul] at h3
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h2, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h3
  rw [← h3]; ring

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_hz {a : XGeo D} (y : YRat a) (q : SplitPt D k) (hU : q.UnitAA) {PP : Pl D.host.E}
    (hI : Formalism.L2.NTheta.IsIdemAt q.e PP) (n : ℕ) (hT : y.Tau (-D.host.xi0 ^ (D.R.m / 2)))
    (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E)) (hnP : ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    ∀ ρ j (h : j + 2 * ρ + 2 = D.R.m), valuation k ((ofSplit q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1 := by
  have hx := val_xi q hU
  have hs := val_star_xi q hU
  have hN := val_nat q hI n hnP
  intro ρ
  induction ρ with
  | zero =>
    intro j h
    change valuation k (q.pr (incA D (star (y.bes j 0 h).ζ ⬝ᵥ (y.bes j 0 h).L.gram *ᵥ (y.bes j 0 h).ζ))) = 1
    have h3 := congrArg (fun x => valuation k (q.pr (incA D x))) (tau_norm y hT j h)
    simp only [hn, map_mul, map_neg, map_pow, Valuation.map_neg, Valuation.map_pow, star_neg, star_pow, hx, hs, hN,
      one_pow, one_mul, mul_one] at h3
    exact h3
  | succ σ ih =>
    intro j h
    have h1 := (y.lnk j σ h).norm
    change star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ = _ at h1
    change valuation k (q.pr (incA D (star (y.bes j (σ + 1) h).ζ ⬝ᵥ (y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))) = 1
    rw [h1, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hx, hs, one_mul, one_mul]
    exact ih _ _

end GlobalTheory.Fam.FramesY

namespace GlobalTheory.Fam.FramesY

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

theorem normalFrames_exist : ∀ {D : D7} (a : XGeo D) (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (n : ℕ), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
    star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((n : ℕ) : D.host.E) → ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
    ∃ (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc := by
  intro D a y βT PP l n hT hn hnP
  have hxi : (ofSplit l.q).xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne (ofSplit l.q)
  have hv : valuation l.k (ofSplit l.q).xi = 1 := val_xi l.q l.unit
  have hsc : ∀ j, (ofSplit l.q).xi ^ (j / 2) ≠ 0 := fun j => pow_ne_zero _ hxi
  have hz := val_hz y l.q l.unit l.idem n hT hn hnP
  have hm := l.hs
  obtain ⟨r, hr⟩ := D.R.m_even
  have key : ∀ j c (hc : j + c = l.s + 1), ∃ F : Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) ((ofSplit l.q).xi ^ (j / 2))
        (l.FX j (by omega)) F) ∧
      ∀ j' (hj : j = j' + 1) ρ h, (ofSplit l.q).IsJacFrame ((y.jac j' ρ h).lev (a.x (j' + 1)).vol)
        ((ofSplit l.q).xi ^ (j' / 2)) ((ofSplit l.q).hz ((y.bes j' ρ h).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
        (hj ▸ F) := by
    intro j c hc
    by_cases hE : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hE
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_bes (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol) (hsc j)
        (l.FX j (by omega))
      obtain rfl : c = 2 * ρ + 1 := by omega
      refine ⟨F, fun ρ' h' => ?_, fun j' hj ρ' h' => absurd h' (by omega)⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
    · have hE' : ∀ ρ, j + 2 * ρ + 2 ≠ D.R.m := fun ρ h => hE ⟨ρ, h⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hE' (r - 1); omega⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ, j' + 2 * ρ + 2 = D.R.m := ⟨(D.R.m - j' - 2) / 2, by have := hE' ((D.R.m - j' - 3) / 2); omega⟩
      obtain ⟨F, hF⟩ := GlobalTheory.LocMod.Witness.exists_jac (ofSplit l.q) ((y.jac j' ρ hρ).lev (a.x (j' + 1)).vol) (hsc j')
        (GlobalTheory.LocMod.Witness.hz_ne (ofSplit l.q) ((y.bes j' ρ hρ).lev (a.x j').vol)) (l.FX (j' + 1) (by omega))
      obtain rfl : c = 2 * ρ := by omega
      refine ⟨F, fun ρ' h' => absurd h' (hE' ρ'), fun j'' hj ρ' h' => ?_⟩
      obtain rfl : j'' = j' := by omega
      obtain rfl : ρ' = ρ := by omega
      exact hF
  refine ⟨fun j c hc => (key j c hc).choose, fun j => (ofSplit l.q).xi ^ (j / 2), fun j => ?_, fun j => ?_,
    fun j ρ h => hz ρ j h, fun j ρ h c hc => (key j c hc).choose_spec.1 ρ h,
    fun j ρ h c hc => (key (j + 1) c hc).choose_spec.2 j rfl ρ h, fun h => ?_⟩
  · rw [map_pow, hv, one_pow]
  · show (ofSplit l.q).xi ^ ((j + 1 + 1) / 2) = (ofSplit l.q).xi ^ (j / 2) * (ofSplit l.q).xi
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]
  · have h2 := (hT l.s h).2
    funext i
    have e1 : ((y.τ l.s h).map (ofSplit l.q).pr *ᵥ fun i => (ofSplit l.q).pr (a.ζ₀ i)) i =
        GlobalTheory.LocMod.Witness.prH (ofSplit l.q) ((y.τ l.s h *ᵥ a.ζ₀) i) :=
      (RingHom.map_mulVec (GlobalTheory.LocMod.Witness.prH (ofSplit l.q)) _ _ i).symm
    rw [e1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_neg, map_pow]
    change -((ofSplit l.q).xi ^ (D.R.m / 2)) * (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i) = _
    rw [show D.R.m / 2 = l.s / 2 + 1 by omega, pow_succ]
    ring

end GlobalTheory.Fam.FramesY
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalizedHaarPairAtFinitePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem normAt_exists : ∀ (D : D7) (V : HSp D) (R : Subgroup (GA D V)), IsClosed (R : Set (GA D V)) → ∀ (L : Lat V),
    IsSelfDualC V L → ∀ Q : Finset (Pl D), ∃ ρ μ, IsNormAt V R L (· ∈ Q) ρ μ := by
  intro D V R hR L hL Q
  obtain ⟨⟨K, hK, hKc, hKo⟩, -⟩ := (_root_.GlobalTheory.FinPl.SetCut.grp_split D V Q).2.2.2.2.2.2.2.2.1 L hL (· ∈ Q)
  have hKG : ∀ g : GA D V, g ∈ K → g ∈ grpAt V (· ∈ Q) := fun g hg => ((hK g).1 hg).1
  have h1 : InK V L (· ∈ Q) 1 := (hK 1).1 K.one_mem

  let S : Set (grpAt V (· ∈ Q)) := {g | InK V L (· ∈ Q) g.1}
  have hSe : S = ((K.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) := by
    ext g; simp [S, Subgroup.mem_subgroupOf, hK]
  have hSo : IsOpen S := hSe ▸ hKo
  have hSc : IsCompact S := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hKc using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact (hK _).2 hg
    · intro hx; exact ⟨⟨x, hKG x hx⟩, (hK x).1 hx, rfl⟩

  let T := R.subgroupOf (grpAt V (· ∈ Q))
  let S' : Set T := {g | InK V L (· ∈ Q) g.1.1}
  have hS'o : IsOpen S' := hSo.preimage continuous_subtype_val
  have hS'c : IsCompact S' := by
    rw [(Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_iff]
    convert hKc.inter_right hR using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨(hK _).2 hg, Subgroup.mem_subgroupOf.1 g.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨⟨x, hKG x hx⟩, Subgroup.mem_subgroupOf.2 hxR⟩, (hK x).1 hx, rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (grpAt V (· ∈ Q)) :=
    ⟨⟨S, hSc⟩, by rw [hSo.interior_eq]; exact ⟨1, h1⟩⟩
  let K₁ : TopologicalSpace.PositiveCompacts T :=
    ⟨⟨S', hS'c⟩, by rw [hS'o.interior_eq]; exact ⟨1, h1⟩⟩
  refine ⟨Measure.haarMeasure K₁, Measure.haarMeasure K₀, inferInstance, inferInstance, ?_, ?_⟩
  · exact Measure.haarMeasure_self (K₀ := K₀)
  · exact Measure.haarMeasure_self (K₀ := K₁)

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormPrescribedValuesClassRepresentative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PerIn

theorem exists_Mt_of_rep_values : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  intro E K ι _ _ _ _ _ _ _ R I Q emb σ _hH w hw hinv
  classical
  let φ : ∀ b, Q.S'.G b → Pol ℂ ι (R.N R.m - 1) → Pol ℂ ι (R.N R.m - 1) := fun b g x =>
    (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam b g)) x
  have φmul : ∀ b (g h : Q.S'.G b) x, φ b (g * h) x = φ b g (φ b h x) := by
    intro b g h x
    simp only [φ, map_mul, Units.val_mul, mul_inv, Module.End.mul_apply, map_smul, smul_smul]
  have hinv' : ∀ c (s : Q.S'.G c.1), s • Q.S'.rep c = Q.S'.rep c → w c = φ c.1 s (w c) :=
    fun c s hs => hinv c ⟨s, hs⟩
  let F : ∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1) := fun b d => φ b (Q.S'.mv b d) (w (Q.S'.cl b d))
  have hcl : ∀ b (g : Q.S'.G b) (d : Q.S'.D b), Q.S'.cl b (g • d) = Q.S'.cl b d := fun b g d =>
    Sigma.ext rfl (heq_of_eq (Quotient.sound (MulAction.mem_orbit d g)))
  have hlaw : ∀ b (g : Q.S'.G b) d, F b (g • d) = φ b g (F b d) := by
    intro b g d
    set c := Q.S'.cl b d with hc
    have hrep : Q.S'.rep (Q.S'.cl b (g • d)) = Q.S'.rep c :=
      congrArg (Q.S'.rp b) (Quotient.sound (MulAction.mem_orbit d g))
    have h1 : Q.S'.mv b (g • d) • Q.S'.rep c = g • d := by
      convert Q.S'.mv_smul b (g • d) using 2; exact hrep.symm
    have h2 := Q.S'.mv_smul b d
    have hs : ((g * Q.S'.mv b d)⁻¹ * Q.S'.mv b (g • d)) • Q.S'.rep c = Q.S'.rep c := by
      rw [mul_smul, h1, _root_.mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
    have hw := hinv' c _ hs
    show φ b (Q.S'.mv b (g • d)) (w (Q.S'.cl b (g • d))) = φ b g (φ b (Q.S'.mv b d) (w c))
    rw [hcl, ← φmul]
    conv_rhs => rw [hw, ← φmul, mul_inv_cancel_left]
  refine ⟨⟨F, fun b d => ⟨?_, fun g _ => hlaw b g d⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hw _))
  · rintro ⟨b, q⟩
    have hq : Q.S'.cl b (Q.S'.rep ⟨b, q⟩) = ⟨b, q⟩ := Sigma.ext rfl (heq_of_eq (Q.S'.rp_spec b q))
    have hr : Q.S'.rep (Q.S'.cl b (Q.S'.rep ⟨b, q⟩)) = Q.S'.rep ⟨b, q⟩ := congrArg (Q.S'.rp b) (Q.S'.rp_spec b q)
    have h1 : Q.S'.mv b (Q.S'.rep ⟨b, q⟩) • Q.S'.rep ⟨b, q⟩ = Q.S'.rep ⟨b, q⟩ := by
      convert Q.S'.mv_smul b (Q.S'.rep ⟨b, q⟩) using 2; exact hr.symm
    show φ b (Q.S'.mv b (Q.S'.rep ⟨b, q⟩)) (w (Q.S'.cl b (Q.S'.rep ⟨b, q⟩))) = w ⟨b, q⟩
    rw [hq]
    exact (hinv' ⟨b, q⟩ _ h1).symm

end GlobalTheory.Mem.Col2.PerIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeTraceAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000


open Formalism.MainNotions.StandardLattice (intAf)

namespace GlobalTheory.Core.Mi.LineSD

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ∈ intAf D.host.F := fun w => by
  rw [map_one]; exact one_mem _

theorem incA_mem_intAE (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, rfl⟩

theorem mul_incA_mem {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (x : 𝓞 D.host.E) :
    a * incA D (x : D.host.E) ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (incA_mem_intAE x)⟩

theorem cA_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha.1
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff, ← GlobalTheory.FinPlLoc.cA_idem, ← map_mul, h]

theorem unit_at {v : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) :
    GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
  have hc : ((T : D.host.E)⁻¹) = algebraMap D.host.F D.host.E ((T : D.host.F)⁻¹) := by simp
  have e : finPart D (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) =
      ((T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [map_mul, GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.finPart_pair]
    show (GlobalTheory.FinPlLoc.ePl D (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((T : D.host.E)⁻¹)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [e]
  refine AddSubgroup.subset_closure ⟨(T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v), fun w => ?_, (1 : 𝓞 D.host.E), ?_⟩
  swap
  · rfl
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · subst hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, if_pos rfl, mul_one]
    show Valued.v (((T : D.host.F)⁻¹ : D.host.F) : w.adicCompletion D.host.F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
    have h1 : w.valuation D.host.F (T : D.host.F) = 1 := by
      have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (T : 𝓞 D.host.F)
      rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hT] at this
      simpa using this
    rw [h1, inv_one]
  · rw [if_neg hw, mul_zero]; exact zero_mem _

def traceLine {S A L : HSp D} (o : OrthDec S A L) (M' : Lat S) (v : GlobalTheory.FinPl.Pl D) :
    AddSubgroup (Fin L.rank → AE D) where
  carrier := {l | (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v)}
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    show o.jB *ᵥ (a + b) ∈ _
    rw [mulVec_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨fun i => zero_mem _, by
    show o.jB *ᵥ 0 ∈ _
    rw [mulVec_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    show o.jB *ᵥ (-a) ∈ _
    rw [mulVec_neg]; exact neg_mem ha.2⟩

theorem exists_isSDAt_line : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M' : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ Λ' : AddSubgroup (Fin L.rank → AE D), GlobalTheory.IwaPlace.IsSDAt L v Λ' ∧ ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) → (l ∈ Λ' ↔ o.jB *ᵥ l ∈ latV S M' (· = v)) := by
  intro D S A L o ζ M' μ T v hζ hμ hline hgram hT
  obtain ⟨hr, hne⟩ := hζ
  obtain ⟨i₀, hall⟩ : ∃ i₀ : Fin L.rank, ∀ i, i = i₀ :=
    ⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega)⟩
  have hs : ∀ {M : Type} [AddCommMonoid M] (f : Fin L.rank → M), ∑ i, f i = f i₀ := fun f =>
    Fintype.sum_eq_single _ fun i hi => absurd (hall i) hi
  have hdot : star ζ ⬝ᵥ L.gram *ᵥ ζ = star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ := by
    simp only [dotProduct, mulVec, hs, Pi.star_apply]; ring
  have hz0 : ζ i₀ ≠ 0 := by
    intro h; apply hne; rw [hdot, h, mul_zero]
  have hsz : star (ζ i₀) ≠ 0 := star_ne_zero.2 hz0
  have hT0 : (T : D.host.E) ≠ 0 := by
    have : T ≠ 0 := by rintro rfl; exact hT (by simp)
    exact_mod_cast this
  have hq : star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ = -(μ * star μ * (T : D.host.E)) := by rw [← hdot, hgram]
  have hjB : ∀ l : Fin L.rank → AE D, o.jB *ᵥ l = (l i₀ * incA D (ζ i₀)⁻¹) • ratV (vecB o ζ) := by
    intro l; funext r
    simp only [OrthDec.jB, rat, vecB, ratV, mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hs]
    rw [map_mul]
    have h1 : incA D (ζ i₀)⁻¹ * incA D (ζ i₀) = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    linear_combination (-(incA D (o.iB r i₀) * l i₀)) * h1
  have hK : ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) →
      (o.jB *ᵥ l ∈ latV S M' (· = v) ↔ l i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v)) := by
    intro l hl
    rw [hjB, hline _ (Ideal.mul_mem_right _ _ (hl i₀))]
    have : incA D μ * (l i₀ * incA D (ζ i₀)⁻¹) = l i₀ * incA D (μ / ζ i₀) := by
      rw [div_eq_mul_inv, map_mul]; ring
    rw [this]
  let Λ' := traceLine o M' v
  have hmem : ∀ l, l ∈ Λ' ↔ (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v) := fun l => Iff.rfl
  have hΛ : ∀ x, x ∈ Λ' ↔ (∀ i, x i ∈ idAt D (· = v)) ∧ x i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v) :=
    fun x => (hmem x).trans (and_congr_right fun hx => hK x hx)
  refine ⟨Λ', ⟨fun y hy => hy.1, ?_, ?_⟩, fun l hl => by rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩⟩
  · obtain ⟨y, hy0, hyint⟩ :=
      exists_integral_multiples ℤ ℚ (L := D.host.E) {μ / ζ i₀}
    replace hyint := hyint _ (Finset.mem_singleton_self _)
    have hn : IsIntegral ℤ ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h, zsmul_eq_mul, Int.cast_natCast] at hyint; exact hyint
      · rw [h, neg_smul, zsmul_eq_mul, Int.cast_natCast] at hyint; simpa using hyint.neg
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun x hx => ?_⟩
    refine (hΛ _).2 ⟨fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i).1
    · have : ((y.natAbs : AE D) • x) i₀ * incA D (μ / ζ i₀) =
          x i₀ * incA D ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
      rw [this]; exact mul_incA_mem (hx i₀) ⟨_, hn⟩
  · intro y hy
    have hherm : ∀ x : Fin L.rank → AE D, GlobalTheory.IwaPlace.hermAt L y x = cA D (x i₀) * incA D (L.gram i₀ i₀) * y i₀ := by
      intro x; simp only [GlobalTheory.IwaPlace.hermAt, hs, gA, rat, Matrix.map_apply]
    have hG : L.gram i₀ i₀ = star (μ / ζ i₀) * (-(T : D.host.E)) * (μ / ζ i₀) := by
      have h1 : L.gram i₀ i₀ = -(μ * star μ * (T : D.host.E)) / (star (ζ i₀) * ζ i₀) := by
        rw [eq_div_iff (mul_ne_zero hsz hz0)]; linear_combination hq
      rw [h1, div_eq_mul_inv μ, star_mul', star_inv₀]
      field_simp
    have hid : ∀ a : AE D, cA D a * incA D (L.gram i₀ i₀) * y i₀ =
        cA D (a * incA D (μ / ζ i₀)) * (y i₀ * incA D (μ / ζ i₀)) * incA D (-(T : D.host.E)) := by
      intro a
      rw [hG]; simp only [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]; ring
    have hay : y i₀ * incA D (μ / ζ i₀) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (hy i₀)
    have he : GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) = GlobalTheory.FinPlLoc.idem D (· = v) := by
      rw [mul_assoc, ← map_mul, show ζ i₀ / μ * (μ / ζ i₀) = 1 by field_simp, map_one, mul_one]
    constructor
    · intro hyΛ x hx
      obtain ⟨-, hyK⟩ := (hΛ y).1 hyΛ
      obtain ⟨-, hxK⟩ := (hΛ x).1 hx
      rw [hherm, hid]
      have := mul_incA_mem (mul_mem_intAt (cA_mem_intAt hxK) hyK) (-(T : 𝓞 D.host.E))
      simpa using this
    · intro h
      refine (hΛ y).2 ⟨hy, ?_⟩
      have hx₁ : (fun _ => GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) : Fin L.rank → AE D) ∈ Λ' := by
        refine (hΛ _).2 ⟨fun i => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
        show GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) ∈ _
        rw [he]; exact GlobalTheory.FinPlLoc.idem_mem_intAt _
      have h1 := h _ hx₁
      rw [hherm, hid] at h1
      rw [he, GlobalTheory.FinPlLoc.cA_idem, (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay] at h1
      have h2 := mul_incA_mem (mul_mem_intAt h1 (unit_at hT)) (-1 : 𝓞 D.host.E)
      have hT' : incA D (-(T : D.host.E)) * incA D ((T : D.host.E)⁻¹) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) = 1 := by
        rw [← map_mul, ← map_mul]; push_cast; rw [neg_mul, mul_inv_cancel₀ hT0]; simp
      have hay' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay
      have e2 : y i₀ * incA D (μ / ζ i₀) * incA D (-(T : D.host.E)) *
          (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) =
          y i₀ * incA D (μ / ζ i₀) := by
        linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * (y i₀ * incA D (μ / ζ i₀))) * hT' + hay'
      rw [e2] at h2; exact h2

end GlobalTheory.Core.Mi.LineSD
end
end

