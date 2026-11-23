module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

open AddMonoidAlgebra in
theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (aconv (e :: l)) : AddMonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (aconv l) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

theorem aconv_nil {G : Type} [AddMonoid G] :
    (AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) : AddMonoidAlgebra ℂ G) = 1 := rfl

theorem aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) :
    (AddMonoidAlgebra.ofCoeff (aconv [c, d]) : AddMonoidAlgebra ℂ G) =
      AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d := by
  rw [aconv_cons, aconv_cons, aconv_nil, mul_one]

theorem aconv_pair_cons {G : Type} [AddMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (aconv [c, d] :: l) = aconv (c :: d :: l) := by
  apply (AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G))
  rw [aconv_cons, aconv_pair, aconv_cons, aconv_cons, mul_assoc]

theorem mem_support_aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) {u : G} (hu : u ∈ (aconv [c, d]).support) :
    ∃ a ∈ c.support, ∃ b ∈ d.support, a + b = u := by
  classical
  have h : (AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d : AddMonoidAlgebra ℂ G).coeff u ≠ 0 := by
    rw [← aconv_pair]; exact Finsupp.mem_support_iff.1 hu
  rw [AddMonoidAlgebra.coeff_mul] at h
  simp only [AddMonoidAlgebra.coeff_ofCoeff] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hab : a + b = u
  · exact ⟨a, ha, b, hb, hab⟩
  · exact absurd (if_neg hab) h2

open MonoidAlgebra in
theorem conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (conv (e :: l)) : MonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (conv l) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
  simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_ofCoeff]
  rfl

theorem conv_nil {G : Type} [Monoid G] :
    (MonoidAlgebra.ofCoeff (conv ([] : List (G →₀ ℂ))) : MonoidAlgebra ℂ G) = 1 := rfl

theorem mul_comm_of_support {G : Type} [Monoid G] (a b : MonoidAlgebra ℂ G)
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, x * y = y * x) : a * b = b * a := by
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.mul_def]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  dsimp only
  rw [h x hx y hy, mul_comm (a.coeff x)]

theorem comm_conv {G : Type} [Monoid G] (E : G →₀ ℂ) (l : List (G →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) :
    (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff (conv l) =
      MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E := by
  induction l with
  | nil => rw [conv_nil, mul_one, one_mul]
  | cons e l ih =>
    have h1 : (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff e =
        MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff E :=
      mul_comm_of_support _ _ fun x hx y hy => h x hx e List.mem_cons_self y hy
    rw [conv_cons, ← mul_assoc, h1, mul_assoc, ih fun x hx e' he' y hy => h x hx e' (List.mem_cons_of_mem _ he') y hy,
      mul_assoc]

section Trc
variable {D : D7} {V : HSp D}

theorem trc_eq_sum (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_single (g : GA D V) (a : ℂ) (f : GA D V → ℂ) : trc (Finsupp.single g a) f = a • rTrans g f := by
  rw [trc_eq_sum, Finsupp.sum_single_index]
  exact zero_smul _ _

theorem trc_zero (f : GA D V → ℂ) : trc (0 : GA D V →₀ ℂ) f = 0 := by
  simp [trc]

theorem trc_add (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (e + e') f = trc e f + trc e' f := by
  simp only [trc_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem trc_apply (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) : trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, Finset.sum_apply, rTrans]

theorem trc_add_right (e : GA D V →₀ ℂ) (f f' : GA D V → ℂ) : trc e (f + f') = trc e f + trc e f' := by
  funext x
  simp only [trc_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem trc_zero_right (e : GA D V →₀ ℂ) : trc e (0 : GA D V → ℂ) = 0 := by
  funext x
  simp [trc_apply]

theorem trc_mul (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc (MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff e' : MonoidAlgebra ℂ (GA D V)).coeff f = trc e (trc e' f) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [MonoidAlgebra.ofCoeff_zero, zero_mul, MonoidAlgebra.coeff_zero, trc_zero, trc_zero]
  | add x y hx hy =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add, trc_add, trc_add, hx, hy]
  | single g a =>
    induction e' using Finsupp.induction_linear with
    | zero => rw [MonoidAlgebra.ofCoeff_zero, mul_zero, MonoidAlgebra.coeff_zero, trc_zero, trc_zero_right]
    | add x y hx hy =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, MonoidAlgebra.coeff_add, trc_add, hx, hy, trc_add, trc_add_right]
    | single h b =>
      rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.coeff_single, trc_single, trc_single, trc_single]
      funext x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem contAut_trc (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ x => ?_, ?_⟩
  · simp only [trc_apply, mul_assoc, hf.1 γ hγ]
  · have : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := funext (trc_apply e f)
    rw [this]
    exact continuous_finsetSum _ fun g _ => (GlobalTheory.Core.Mi.BotPin.isContAut_rTrans g hf).2.const_smul (e g)

end Trc

end GlobalTheory.QValOuter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabMove

variable {D : D7}

def IntG (V : HSp D) (g : GA D V) : Prop := ∀ i j, finPart D (Formalism.L2.Theta.mt V g i j) ∈ intAE D

theorem IntG.inv {V : HSp D} (hV : V.gram = 1) {g : GA D V} (h : IntG V g) : IntG V g⁻¹ := by
  have e : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at e
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have e3 : Formalism.L2.Theta.mt V g⁻¹ = ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ := by
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V g⁻¹), ← e, Matrix.mul_assoc, e2, Matrix.mul_one]
  intro i j
  rw [e3, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MovedIdem.finPart_cA]
  exact GlobalTheory.MovedIdem.sigR_mem_intAE (h j i)

theorem intG_of_moves {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V}
    (h : GlobalTheory.AdForm.Moves V hn k (Formalism.L2.Col.stdLat D.host.E n)) : IntG V k⁻¹ := by
  subst hn
  intro i j
  have h1 := (h (Pi.single j 1)).1 (fun a _ => by
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _) i
  refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
  have e : (fun a => eToEAf D ((Pi.single j 1 : Fin V.rank → D.host.E) a)) = Pi.single j 1 := by
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [e, Matrix.mulVec_single_one] at h1
  exact h1

theorem mem_hatV_iff {n : ℕ} (u : Fin n → GlobalTheory.Ker.AfE D) :
    u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) ↔ ∀ i, u i ∈ intAE D := by
  constructor
  · intro hu i
    induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (GlobalTheory.SW.Base.mem_stdL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hu
    rw [← Finset.univ_sum_single u]
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, (Pi.single i z : Fin n → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (GlobalTheory.SW.Base.mem_stdL _).2 fun b => ?_, ?_⟩
        · rw [Pi.single_apply]
          split_ifs
          · exact x.2
          · exact isIntegral_zero
        · funext b
          rw [Pi.single_apply, Pi.single_apply]
          split_ifs
          · rfl
          · rw [TensorProduct.tmul_zero]
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
      | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy
    exact key _ (hu i)

theorem isMov_of_intG {V : HSp D} {k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) (GlobalTheory.SW.stdL D.host.E V.rank) (GlobalTheory.SW.stdL D.host.E V.rank) := by
  have key : ∀ g, IntG V g → ∀ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank),
      GlobalTheory.Ker.fmt V g *ᵥ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank) := fun g hg u hu =>
    (mem_hatV_iff _).2 fun i => sum_mem (t := Finset.univ) fun j _ => GlobalTheory.GeoActCompare.TameConj.mul_mem_intAE (hg i j) ((mem_hatV_iff _).1 hu j)
  intro u
  refine ⟨fun hu => ⟨_, key _ h' u hu, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_mulVec, GlobalTheory.Ker.fmt, GlobalTheory.Ker.fmt, ← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel,
      GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    exact key _ h u₀ h0

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]

theorem moves_of_mul {V : HSp D} {n : ℕ} (hn : V.rank = n) {g k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) {N}
    (hN : GlobalTheory.AdForm.Moves V hn (g * k) N) : GlobalTheory.AdForm.Moves V hn g N := by
  have key : ∀ a, IntG V a → ∀ u : Fin n → EF D, (∀ i, u i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ i, (finM V hn a *ᵥ u) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha u hu i =>
    sum_mem (t := Finset.univ) fun j _ => mul_mem
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (ha ((finCongr hn).symm i) ((finCongr hn).symm j))) (hu j)
  intro x
  rw [hN x]
  constructor
  · intro hx
    have := key k h _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  · intro hx
    have := key _ h' _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, ← _root_.mul_inv_rev] at this

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem coe_stdL (n : ℕ) : (GlobalTheory.SW.stdL D.host.E n : Set (Fin n → D.host.E)) = intVec D n :=
  Set.ext fun x => GlobalTheory.SW.Base.mem_stdL x

theorem om_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {μ : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T μ μ om)
    (hu : ∀ v ε, GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.UnramAt ε μ) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f) {k : GA D S} {k' : GA D T}
    (hk : k ∈ GfC S) (hk' : k' ∈ GfC T) (a : IntG S k) (a' : IntG T k') :
    ∃ x y, IsDetRoot S k x ∧ IsDetRoot T k' y ∧ om (k, k') f = (((μ x)⁻¹ * μ y : Circle) : ℂ) • f := by
  have m := isMov_of_intG a (a.inv hP.gS)
  have m' := isMov_of_intG a' (a'.inv hP.gT)
  have sS := GlobalTheory.Ker.Base.selfDualC_stdL hP.gS
  have sT := GlobalTheory.Ker.Base.selfDualC_stdL hP.gT
  obtain ⟨x, hx, rx⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D S _ sS k hk m
  obtain ⟨y, hy, ry⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T _ sT k' hk' m'
  have hc : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hV]
      simp
    rw [this]
    exact GlobalTheory.AdTh.isCartanInv_one_splitStab _
  refine ⟨x, y, rx, ry, GlobalTheory.FinVac.om_vacuum_finite D S T ψ θ hP.inf hP.sigS hP.sigT μ μ om hW
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) (fun v ε hv => ⟨hu v ε hv, hu v ε hv⟩) (fun _ => 1) (fun _ => 1)
    (hc S hP.gS) (hc T hP.gT) _ _ sS sT f ?_ k hk k' hk' m m' x y hx hy rx ry⟩
  rwa [coe_stdL, coe_stdL]

end GlobalTheory.AdForm.StabMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

namespace GlobalTheory.FinPl

theorem movesLocal_supp_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (v : Pl D)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L (fun _ => True) ↔ y ∈ latV S L (· = v) := by
  have hT := ((_root_.GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L y hL
  have hV := ((_root_.GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  have hsub : ∀ i, y i ∈ idAt D (fun _ => True) := by
    intro i
    have h := hy i
    simp only [idAt, Submodule.mem_inf] at h ⊢
    refine ⟨h.1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w trivial e he⟩
  · rintro ⟨_, h⟩
    refine ⟨hsub, fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (_root_.GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem movesLocal : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ g : GA D S, (GlobalTheory.FinPl.Moves S g L L (fun _ => True) ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L L (· = v)) := by
  intro D S L hL g
  have hmv : ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
    intro P y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  constructor
  · intro h v y hy
    have hyT : ∀ i, y i ∈ idAt D (fun _ => True) := by
      intro i
      have h' := hy i
      simp only [idAt, Submodule.mem_inf] at h' ⊢
      refine ⟨h'.1, ?_⟩
      simp only [Submodule.mem_iInf]
      intro w
      exact absurd trivial w.2
    rw [← movesLocal_supp_iff S L hL.1 v y hy, ← movesLocal_supp_iff S L hL.1 v _ (hmv _ y hy)]
    exact h y hyT
  · intro h y hy
    have hT := fun z => ((_root_.GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L z hL.1
    rw [hT y, hT (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w (e • y) hey).1 (hy' w trivial e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w trivial e he

end GlobalTheory.FinPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaQEmpty
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepLevLaw

theorem omegaQ_empty {D : D7} {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (fun PP hP => absurd hP (Finset.notMem_empty PP))]
  simp


set_option maxHeartbeats 1000000 in
open Classical in
theorem stepLevLaw : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → ∀ ω, IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω → ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → ∀ κ ∈ levS s.V s.β s.L, κ ∈ GfC s.V ∧ ω (κ, 1) f = Lev.levChi s.V s.β s.L κ • f := by
  intro D c hc k s s' hs hs' ω hW ξ f₀ f hv κ hκ
  refine ⟨hκ.1, ?_⟩
  have hPg : s.L.Pg = c.Pg := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← hPg, ← Finset.union_empty s.L.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := _root_.GlobalTheory.ChainOnto.levRes_step D c hc k k.isLt
  have hlev : Lev.finE s.V κ ∈ lev D.sp.cm s.V.gram s.β s.L := hκ.2
  have sg : Lev.finE s.V κ ∈ St s.β := parLev_St hlev.1
  have sh : Lev.finE s'.V 1 ∈ St s'.β := by rw [map_one]; exact Subgroup.one_mem _
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
    hs.selfDual hs'.selfDual hs.frame hs'.frame hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hκ.1 (Subgroup.one_mem _) sg sh
  set G : ∀ PP : Pl D.host.E, GL (Fin s.V.rank) (kP PP) := fun PP => redFn s.β PP (Lev.finE s.V κ) with hG
  have h1' : ω (κ, 1) f₀ = ((∏ PP ∈ c.Pg, c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_inv, mul_one, hG]
  have hoG := _root_.GlobalTheory.ChainOnto.RightMove.omegaG_mul_right D s.V.rank s'.V.rank s.L (c.chi (↑k + 1)) G (fun PP hP => parLev_g hlev.1 hP) hlev.2
  have h2 := _root_.GlobalTheory.ThetaMove.om_theta_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (_root_.GlobalTheory.SchrTheta.isTheta_placeModel D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (_root_.GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame κ 1 sg sh) _
    ((s.L.P.chi ⟨_, hlev.2⟩ * (∏ PP ∈ s.L.Pg, ∏ i ∈ Finset.range s.L.s, s.L.cg (i + 1) PP (dBlk (blkOf s.L.r s.L.t) (i + 1) (G PP))) *
      ∏ PP ∈ s.L.Pg, (c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := _root_.GlobalTheory.FrameRed.frMapO_actO_int_red D s.V s'.V s.β s'.β κ 1 sg sh x
      have i0 : IsHalf e (actO s.V s'.V κ⁻¹ 1⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), omegaQ_empty, omegaQ_empty, mul_one, mul_one]
        simp only [map_one, redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        exact hoG (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2]
  congr 1
  unfold Lev.levChi levFn
  rw [hQ, Finset.prod_empty, mul_one, extendOne_of_mem _ hlev.2, ← Units.val_mul, ← hPg, Finset.prod_inv_distrib]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.ChainOnto.StepLevLaw

end
end

