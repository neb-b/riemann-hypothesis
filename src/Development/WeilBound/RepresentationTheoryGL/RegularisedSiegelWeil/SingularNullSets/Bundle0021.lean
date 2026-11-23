module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0019
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) (γ : hermA D n)
    (hγ : γ ∈ ratHerm D n) (x : hermA D n) : chn ψ β (γ + x) = chn ψ β x := by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem per_nb {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n)
    (γ : hermA D n) (hγ : γ ∈ ratHerm D n) (x : hermA D n) : F (nb (γ + x) * g) = F (nb x * g) := by
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) (x : Mx D n n) (β : HermE D n) :
    pch ψ x (rat β.1) = ψ (GlobalTheory.CompanionTheory.FourierN.pr β.1 x) := by
  show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))
  rw [Matrix.trace_mul_comm]

theorem fc_eq (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam := rfl

theorem chn_shift (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b x : hermA D n) :
    chn ψ β b = chn ψ β (b + x) * pch ψ x.1 (rat β.1) := by
  rw [chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]
  abel

set_option synthInstance.maxHeartbeats 400000 in
theorem fc_nb_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) (β : HermE D n) (x : hermA D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β (nb x * g) = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  have hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b := fun γ hγ b => by
    rw [per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]
  have h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam :=
    GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x
  rw [fc_eq, fc_eq, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]
  ring

set_option synthInstance.maxHeartbeats 400000 in
theorem integrableOn_fc {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) (β : HermE D n) (h : G D n) :
    IntegrableOn (fun b => F (nb b * h) * chn ψ β b) 𝓖 lam := by
  obtain ⟨hnb, hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h)
    (per_nb hinv hnb h)
  refine Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top)
    ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)
  rw [norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]
  exact hM b

theorem fc_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (β : HermE D n)
    {x : hermA D n} (hx : IntAt v x) {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb F β g = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  rw [← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * g) * _ = F (nb b * (nb x * g)) * _
  rw [commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]

theorem fc_cutR {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (C : Cut D n v) (β : HermE D n) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  have e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b =
      ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) := fun b => by
    unfold cutR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]
  calc fc ψ lam 𝓖 nb (cutR nb C F) β g
      = ∫ b in 𝓖, ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_congr_ae (.of_forall e)
    _ = ∑ x ∈ C.s, ∫ b in 𝓖, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_finsetSum _ fun x _ => (integrableOn_fc hψ hC hF hinv β (nb x * g)).const_mul _
    _ = ∑ x ∈ C.s, C.co x * fc ψ lam 𝓖 nb F β (nb x * g) :=
        Finset.sum_congr rfl fun x _ => integral_const_mul _ _
    _ = ∑ x ∈ C.s, C.co x * (pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g) :=
        Finset.sum_congr rfl fun x _ => by rw [fc_nb_mul hψ hC hinv]
    _ = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
        rw [cutF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

end PositivityTheory.Rg.Rsw.L.LCutLow

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem tsum_GQ (V : HSp D) (n : ℕ) (γ : GA D V) (hγ : γ ∈ GQ V) (F : Mx D V.rank n → ℝ≥0∞) :
    ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (mm (mt V γ) (rat x.1)) =
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (rat x.1) := by
  obtain ⟨g, hg⟩ := mem_ratMx.1 ((mem_GQ_iff V γ).1 hγ)
  obtain ⟨g', hg'⟩ := mem_ratMx.1 ((mem_GQ_iff V γ⁻¹).1 (inv_mem hγ))
  have h1 : g' * g = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_inv_mul V γ)
  have h2 : g * g' = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_mul_inv V γ)
  have hu : IsUnit g.det := isUnit_iff_exists_inv.2 ⟨g'.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩
  have hu' : IsUnit g'.det := isUnit_iff_exists_inv.2 ⟨g.det, by rw [← Matrix.det_mul, h1, Matrix.det_one]⟩
  let e : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} ≃
      {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} :=
    { toFun := fun x => ⟨g * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g x.1 hu]; exact x.2⟩
      invFun := fun x => ⟨g' * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g' x.1 hu']; exact x.2⟩
      left_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h1, Matrix.one_mul])
      right_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]) }
  rw [← e.tsum_eq (fun x => F (rat x.1))]
  refine tsum_congr fun x => ?_
  show F _ = F (rat (g * x.1))
  rw [rat_mul, hg]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intOpen (V : HSp D) : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
    ∀ k ∈ U, ∀ i j, finPart D (mt V k i j) ∈ intAE D := by
  have hfc : Continuous (finPart D) := GlobalTheory.Member.continuous_finPart D
  have hint : ∀ (A B : Mx D V.rank V.rank), (∀ i j, finPart D (A i j) ∈ intAE D) → (∀ i j, finPart D (B i j) ∈ intAE D) →
      ∀ i j, finPart D ((A * B) i j) ∈ intAE D := by
    intro A B hA hB i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    exact sum_mem fun l _ => by rw [map_mul]; exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hA i l) (hB l j)
  have hone : ∀ i j, finPart D ((1 : Mx D V.rank V.rank) i j) ∈ intAE D := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact (by simpa using GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE (D := D) 1)
    · rw [map_zero]; exact zero_mem _
  let U : Subgroup (GA D V) :=
    { carrier := {k | (∀ i j, finPart D (mt V k i j) ∈ intAE D) ∧ ∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D}
      one_mem' := by
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V 1 = 1 from rfl]; exact hone i j
        · rw [inv_one, show mt V 1 = 1 from rfl]; exact hone i j
      mul_mem' := by
        rintro k l ⟨hk, hk'⟩ ⟨hl, hl'⟩
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V (k * l) = mt V k * mt V l from rfl]; exact hint _ _ hk hl i j
        · rw [mul_inv_rev, show mt V (l⁻¹ * k⁻¹) = mt V l⁻¹ * mt V k⁻¹ from rfl]; exact hint _ _ hl' hk' i j
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        exact ⟨hk', by simpa using hk⟩ }
  refine ⟨U, ?_, fun k hk => hk.1⟩
  have hmt : Continuous (mt V) := GlobalTheory.MixModel.continuous_mt V
  have hmti : Continuous fun k : GA D V => mt V k⁻¹ := hmt.comp continuous_inv
  have hopen : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have h1 := GlobalTheory.CompanionTheory.Ipf.Bdd.isOpen_nsmul_mem (D := D) 1
    simp only [one_nsmul] at h1
    exact h1
  have e : (U : Set (GA D V)) = (⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k i j)) ⁻¹' {z | z ∈ intAE D}) ∩
      ⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k⁻¹ i j)) ⁻¹' {z | z ∈ intAE D} := by
    ext k; simp [U]
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmt)))
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmti)))

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem theta_cont (hθ : IsInfFam θ) (Φ : schwartzA θ W.rank n)
    (hcont : Continuous fun u : G D n × Mx D W.rank n => (ω u.1 Φ).1 u.2)
    (hmaj : ∀ C : Set (G D n), IsCompact C → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ C, ∀ x, ‖(ω g Φ).1 x‖ ≤ ‖M x‖) :
    Continuous fun u : G D n × GA D W => theta ω Φ u.1 u.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨Qg, hQg, hpg⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Qh, hQh, hph⟩ := exists_compact_mem_nhds p.2
  obtain ⟨M, hM, hMb⟩ := hmaj Qg hQg
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajLoc.summable_bound D θ hθ W.rank n
  obtain ⟨-, K, hK, hC⟩ := _root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank n M (_root_.GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank n M hM)
  obtain ⟨K', hK', hmul⟩ := _root_.GlobalTheory.MajMul.maj_mul_le D θ hθ W n Qh hQh K hK
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  obtain ⟨b, hb, hb'⟩ := hN K' {0} hK' isCompact_singleton
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      Continuous fun u : G D n × GA D W => (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := fun ξ =>
    hcont.comp (continuous_fst.prodMk (((GlobalTheory.LatNhds.continuous_mt_inv W).comp continuous_snd).matrix_mul
      continuous_const))
  have hon : ContinuousOn (fun u : G D n × GA D W => ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))) (Qg ×ˢ Qh) := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hb.mul_left (|C| * C₂)) fun ξ u hu => ?_
    have h1 := hMb u.1 hu.1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h2 := hC (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h3 := hmul' u.2 hu.2 (rat ξ : Mx D W.rank n)
    have h4 := hb' 0 rfl ξ
    rw [zero_add] at h4
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    calc ‖(ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))‖
        ≤ C * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := h1.trans h2
      _ ≤ |C| * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hm0
      _ ≤ |C| * (C₂ * GlobalTheory.Unf.maj θ K' N (rat ξ : Mx D W.rank n)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ ≤ |C| * (C₂ * b ξ) := by gcongr
      _ = |C| * C₂ * b ξ := by ring
  exact hon.continuousAt (prod_mem_nhds hpg hph)

theorem theta_full (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' g h = ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  unfold theta
  have hsupp : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E => (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆
      {y : Matrix (Fin W.rank) (Fin n) D.host.E | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hr
    exact hξ (term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hr)
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

theorem bound_triv (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (hLB : LatBound) (hθ : IsInfFam θ)
    (hmaj : ∀ Q : Set (G D n), IsCompact Q → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ Q, ∀ x, ‖(ω g Ψ').1 x‖ ≤ ‖M x‖)
    (Q : Set (G D n)) (hQ : IsCompact Q) :
    ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 → ∀ h, ‖theta ω Ψ' g h‖ ≤ b := by
  obtain ⟨M, hM, hMb⟩ := hmaj Q hQ
  obtain ⟨B, hB⟩ := hLB D θ hθ W n M hM
  refine ⟨B, fun g hg hgv h => ?_⟩
  rw [theta_full hω hnb C hC Ψ Ψ' hΨ hΨ' hgv h]
  have e : ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ₑ ≤ B :=
    (enorm_tsum_le_tsum_enorm).trans ((ENNReal.tsum_le_tsum fun y => by
      have := hMb g hg (mm (mt W h⁻¹) (rat y.1))
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this).trans (hB h))
  have e2 : ENNReal.ofReal ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm, ENNReal.ofReal_coe_nnreal]; exact e
  exact (ENNReal.ofReal_le_ofReal_iff B.2).1 e2

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

