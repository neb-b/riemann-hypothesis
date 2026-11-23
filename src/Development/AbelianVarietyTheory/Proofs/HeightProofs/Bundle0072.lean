module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullOfXiRec
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_full_of_xiRec : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ de, XiRec D p de → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ XiTilde TF.xi de ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hcan p hp P hP de hde
  obtain ⟨xi, hxi, ht⟩ := _root_.GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde D p de hp.own hde
  obtain ⟨dd, TF, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol D J T hJ hT hc hcan p hp P hP xi hxi
  exact ⟨dd, TF, h1, h2, h3, h4 ▸ ht, h5⟩

end GlobalTheory.FinalJoin2.FullExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem twDat_psi_valuesIn_LL : ∀ (B : Base) (T : TwDat B), Coh B T → ∀ v, (T.psi v).ValuesIn 0 B.embLL := by
  intro B T hC v w _
  obtain ⟨z, hz⟩ := hC.roots v
  haveI : NeZero (B.places.resChar v ^ T.k v) := ⟨pow_ne_zero _ (B.places.resChar_prime v).ne_zero⟩
  have hpow : ∀ (χ : Formalism.L2.Host.HChar B.host.E) (m : ℕ), (χ ^ m).val w = χ.val w ^ m := by
    intro χ m
    induction m with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ m ih => rw [pow_succ, Formalism.L2.Host.HChar.val_mul, ih, pow_succ]
  have h1 : (((T.psi v).val w : ℂˣ) : ℂ) ^ (B.places.resChar v ^ T.k v) = 1 := by
    have hord : T.psi v ^ (B.places.resChar v ^ T.k v) = 1 := T.psi_ord v
    have h0 : (T.psi v ^ (B.places.resChar v ^ T.k v)).val w = (1 : Formalism.L2.Host.HChar B.host.E).val w := by rw [hord]
    rw [hpow] at h0
    rw [← Units.val_pow_eq_pow_val, h0]
    rfl
  have hz' := hz.map_of_injective B.embLL.injective
  obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h1
  refine ⟨z ^ i, ?_⟩
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rw [map_pow, hi]

end GlobalTheory
end

