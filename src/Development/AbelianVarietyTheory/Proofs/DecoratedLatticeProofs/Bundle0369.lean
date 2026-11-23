module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalCharacterIsUnramifiedOfHeckeUnram
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinUnram

open GlobalTheory.SplitLinAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem off_idl (p : SplitPt D k) (a : kˣ) : (1 - p.e) * ((idl p a : (AE D)ˣ) : AE D) = 1 - p.e := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination (-1 : AE D) * ha + he

theorem e_mul_idl (p : SplitPt D k) (a : kˣ) : p.e * ((idl p a : (AE D)ˣ) : AE D) = p.sec a := by
  have he : p.e * p.e = p.e := p.split.1
  have ha := sec_self p (a : k)
  rw [idl_val]
  linear_combination ha - he

theorem map_e_eq_zero (p : SplitPt D k) {R : Type} [CommRing R] (f : AE D →+* R) (h : f (p.e + cA D p.e) = 0) :
    f p.e = 0 := by
  have h1 : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, p.split.1, p.split.2.1, add_zero]
  rw [h1, RingHom.map_mul, h, mul_zero]

theorem infPart_e (p : SplitPt D k) : infPart D p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, -⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem compAt_e (p : SplitPt D k) {w : Pl D} (hw : w ≠ p.v) : compAt D w p.e = 0 := by
  obtain ⟨ε, ⟨α, hε, -, h0⟩, h⟩ := p.above
  refine map_e_eq_zero p _ ?_
  rw [h, hε]
  change evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  rw [h0 w hw]
  exact TensorProduct.zero_tmul _ _

theorem idl_int (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) :
    finPart D ((idl p a : (AE D)ˣ) : AE D) ∈ intAE D := by
  rw [idl_val, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one]
  refine add_mem ((p.int_iff _).1 ha) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)) ?_)
  rw [← sec_one]
  exact (p.int_iff 1).1 (one_mem _)

theorem absFin_idl (p : SplitPt D k) {a : kˣ} (ha : (a : k) ∈ 𝒪[k]) (ha' : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k]) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p a) = 1 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have key : ∀ b : kˣ, (b : k) ∈ 𝒪[k] →
      Valued.v ((Units.map π.toMonoidHom (idl p b) : (Fv D.host.F v)ˣ) : Fv D.host.F v) ≤ 1 := fun b hb =>
    GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 (by rw [e_mul_idl]; exact (p.int_iff _).1 hb))
  have a1 := key a ha
  have a2 := key _ ha'
  rw [GlobalTheory.SplitLinear.absFin_split D p.e v π p.split hπ _ (off_idl p a)]
  rw [MonoidHom.map_inv, MonoidHom.map_inv] at a2
  generalize Units.map π.toMonoidHom (idl p a) = y at a1 a2 ⊢
  have hne : Valued.v (y : Fv D.host.F v) ≠ 0 := by simp
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at a2
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, le_antisymm a1 a2]

theorem lam_unram : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ : (AE D)ˣ →* Circle) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v → IsUnram (GlobalTheory.SplitLinAt.lam p χ r) := by
  intro D k _ _ _ _ p χ r hχ a ha
  have h1 : (a : k) ∈ 𝒪[k] := ha.le
  have h2 : ((a⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    change valuation k ((a⁻¹ : kˣ) : k) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  have h3 : χ (idl p a) = 1 :=
    hχ _ (GlobalTheory.SplitLinear.off_norm'' _ (infPart_e p) (off_idl p a))
      (fun w hw => GlobalTheory.SplitLinear.off_norm'' (compAt D w) (compAt_e p hw) (off_idl p a)) (idl_int p h1)
      (by rw [← MonoidHom.map_inv]; exact idl_int p h2)
  refine Units.ext ?_
  rw [lam_val, h3, absFin_idl p h1 h2, Real.one_rpow]
  simp

end GlobalTheory.SplitLinUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.OffPlace

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_of_idOff (p : SplitPt D k) {a : Formalism.L2.Theta.AE D} (ha : a ∈ idOff D (· = p.v)) : p.pr a = 0 := by

  have hv : compAt D p.v a = 0 := by
    rw [idOff, Submodule.mem_iInf] at ha
    exact ha ⟨p.v, rfl⟩
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  obtain ⟨α, hα, hαv, hαw⟩ := hε
  have hparts := placeIdempotent_infinite_and_finite_components D p.v ε α hα

  have hεa : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [map_mul, hparts.1, zero_mul]
    · intro w
      rw [map_mul, hparts.2 w]
      by_cases hw : w = p.v
      · subst hw
        rw [hv, mul_zero]
      · rw [hαw w hw, TensorProduct.zero_tmul, zero_mul]

  have hea : p.e * a = 0 := by
    have : p.e * algebraMap (AF D.host.F) (AE D) ε = p.e := by
      rw [← hsum, mul_add, hee, hec, add_zero]
    rw [← this, mul_assoc, hεa, mul_zero]
  rw [← p.pr_sec (p.pr a), p.sec_pr, hea, map_zero]

theorem map_pr_of_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  intro D k _ _ _ _ p S n _ _ β κ g h
  set γ := κ * (β.gl g)⁻¹ with hγ

  have hq : (mt S γ).map (Ideal.Quotient.mk (idOff D (· = p.v))) = 1 := by
    rw [grpOff, congGrp, MonoidHom.mem_ker] at h
    have := congrArg (fun M : GL (Fin S.rank) (AE D ⧸ idOff D (· = p.v)) => M.val) h
    simpa [Formalism.L2.Theta.mt] using this

  have hγ1 : (mt S γ).map p.pr = 1 := by
    ext i j
    have hij := congrFun (congrFun hq i) j
    have hmem : mt S γ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D (· = p.v) := by
      rw [← Ideal.Quotient.eq]
      rw [Matrix.map_apply] at hij
      rw [hij, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := pr_of_idOff p hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hκ : κ = γ * β.gl g := by rw [hγ, inv_mul_cancel_right]
  have hmt : mt S κ = mt S γ * mt S (β.gl g) := by
    rw [hκ]
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  rw [hmt, Matrix.map_mul, hγ1, one_mul, β.gl_mat g]

end GlobalTheory.AdForm.OffPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.AdForm

theorem stdT_levelPrime_mem_v : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS i
  obtain ⟨e, he⟩ := hS.1
  have hv := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) (he i)
  have hT := GlobalTheory.ColNorms.BadPrimes.T_mem (GlobalTheory.BasePrimes.primes_ok B X).1 (e i).2
  rw [hv]
  show _ ∈ Ideal.under _ _
  rw [Ideal.mem_under, map_natCast]
  exact hT

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.AdForm

def intVecSub (D : D7) (n : ℕ) : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun {x y} hx hy k => (hx k).add (hy k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c {x} hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact c.2.mul (hx k)

theorem coe_intVecSub (D : D7) (n : ℕ) : ((intVecSub D n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := rfl

theorem stdHom_map_splitIdem : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  intro D S T a ha u hu
  have h := Formalism.IndefR.Fin.latO_map_splitIdem S T (intVecSub D S.rank) (intVecSub D T.rank) ha
    (u := u) (by rw [coe_intVecSub, coe_intVecSub]; exact hu)
  rw [coe_intVecSub, coe_intVecSub] at h
  exact h

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftFockVec

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem ptAt_isFockVec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h'
  obtain ⟨⟨hψ, hv⟩, -⟩ := hlv
  have hθ : IsInfFam R.θ := hv.inf
  obtain ⟨⟨p, hp⟩, -⟩ := hv.norm
  obtain ⟨-, hθf, hS, hvac⟩ := GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h p.1 p.2 hp
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ)
  set Ap := aPlusAll (heisO R.ψ (Vc D i) (Wc D i)) R.θ (fun τ => cplxO ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) (cart (R.MW i σ) τ)) (R.BV i) BW with hAdef
  have hadd : ∀ g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (g + g') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (a • g) :=
    fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (Ap k g) :=
    fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i' j g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (Ap j g) = Ap j (Ap i' g) :=
    fun i' j _ h => aPlus_comm' hψ hθ i'.1 _ hS hT j.1 _ h
  have Aadd : ∀ i' g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      Ap i' (g + g') = Ap i' g + Ap i' g' :=
    fun i' _ _ h h' => aPlus_add hψ hθ i'.1 _ _ h h'
  have Asm : ∀ i' (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (a • g) = a • Ap i' g :=
    fun i' a _ h => aPlus_smul hψ hθ i'.1 _ _ a h
  have hpt' : ∀ Q', ptAt R i σ BW f Q' = pureTensorL Ap f Q' := fun _ => rfl
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ c' : FVar D (Wc D i).rank (Vc D i).rank → ℂ, ∀ Q',
      annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) z (pureTensorL Ap f Q') =
        pureTensorL Ap f (∑ k, c' k • MvPolynomial.pderiv k Q') := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir (Vc D i) (Wc D i) τ z k.1 (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir (Vc D i) (Wc D i) τ (cplxO 1 (cart (R.MW i σ) τ) z) k.1
          (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ))), fun Q' => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hθf (hvac τ z) Q'
  refine ⟨hpt Q, Q.totalDegree + 1, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ Q' : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ,
      l.foldr (fun p g => annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ p.1 (cplxO 1 (cart (R.MW i σ) p.1)) p.2 g)
          (pureTensorL Ap f Q) = pureTensorL Ap f Q' ∧
        ∀ n : FVar D (Wc D i).rank (Vc D i).rank →₀ ℕ, Q.totalDegree < n.degree + l.length → Q'.coeff n = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨Q, rfl, fun n hn => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h2 : Q.totalDegree < n.degree := by simpa using hn
      exact h2
    | cons q l ih =>
      obtain ⟨Q', hQ', hQc⟩ := ih
      obtain ⟨c', hc'⟩ := hder q.1 q.2
      refine ⟨∑ k, c' k • MvPolynomial.pderiv k Q', ?_, fun n hn => ?_⟩
      · rw [List.foldr_cons, hQ', hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c' Q' (Q.totalDegree - l.length)
          (fun n' hn' => hQc n' (by omega)) n ?_
        simp only [List.length_cons] at hn
        omega
  obtain ⟨Q', hQ', hQc⟩ := key l
  have hQ0 : Q' = 0 := MvPolynomial.ext _ _ fun n => by
    simpa using hQc n (by rw [hl]; omega)
  show l.foldr _ (ptAt R i σ BW f Q) = 0
  rw [hpt', hQ', hQ0, map_zero]

end GlobalTheory.LiftFockVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Aniso

theorem thetaKernel_rationalSource_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (c : GA D S) (h : GA D T) :
    thetaKO om (γ * c) h f = thetaKO om c h f := by
  unfold thetaKO
  have e : om (γ * c, h) = om (γ, (1 : GA D T)) * om (c, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (GQ T).one_mem _ (hω.om_pres (c, h) f hf)

end GlobalTheory.Core.Rk.Aniso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

open GlobalTheory.StepLaw


open Classical in
theorem levRes_step : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, (∀ PP ∈ c.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (c.chi (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (c.chi (k + 1) PP)⁻¹) ∧ GlobalTheory.StepLaw.UnrOff (c.chS (k + 1)) c.Pg ∧ GlobalTheory.StepLaw.UnrOff (c.chT (k + 1)) c.Pg := by
  intro D c hc k hk
  obtain ⟨H, hEq, hres⟩ := hc.res ⟨k, hk⟩
  have hμR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1)) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP =>
    (_root_.GlobalTheory.ResLoc.resAt_of_chrEq D _ H hEq PP).1 _ (_root_.GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP _ (hres PP hP)) (hres PP hP)
  have hμU : UnrOff (c.μ (k + 1)) c.Pg := fun v ε hε hv =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ H hEq v ε hε fun P hP =>
      (GlobalTheory.ChrTie.unrAt_iff_and_val_eq D _ H hEq P).1.1 (hc.unr ⟨k, hk⟩ P fun hm => by
        obtain ⟨PP, hPP, he⟩ := Finset.mem_image.1 hm
        exact hv PP hPP (he.trans hP))
  have hη : UnramEverywhere D c.η := hc.chars.2.1
  have hηR : ∀ PP, ResAt c.η⁻¹ PP 1 := fun PP => by
    have := (GlobalTheory.ExportSeries.TupleChars.resAt_of_unramEverywhere hη PP).inv
    rwa [inv_one] at this
  have hηU : UnrOff c.η⁻¹ c.Pg := UnrOff.inv fun v ε hε _ => GlobalTheory.AdTh.unr_of hη hε
  have hmR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1) * c.η⁻¹) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP => by
    have := (hμR PP hP).mul (hηR PP)
    rwa [mul_one] at this
  have hmU : UnrOff (c.μ (k + 1) * c.η⁻¹) c.Pg := hμU.mul hηU
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs
  · exact ⟨fun PP hP => ⟨hmR PP hP, hμR PP hP⟩, hmU, hμU⟩
  · exact ⟨fun PP hP => ⟨hμR PP hP, hmR PP hP⟩, hμU, hmU⟩

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceWeil

theorem vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu hfix
    have e := hW.om_heis g h u f hf.1
    rw [hfix, GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu)] at e
    exact e.symm
  exact ⟨hW.om_pres _ f hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem combAt_eg {D : D7} {c : Comm D} {v : VCom c} (Gi : GLoc v) (j : ℕ) (hj : j + 1 < D.R.m) :
    CombAt (· = Gi.q.v) (Gi.eg j) := by
  have hs := Gi.hs
  intro u hu a b
  have h1 := (Gi.eg_is j (Gi.s - j) (by omega)).1 u hu a b
  obtain ⟨ε, hε, hsum⟩ := Gi.q.above
  exact ((GlobalTheory.FinPl.placeIdem_acts D Gi.q.v ε hε).1 _).2 (hsum ▸ h1)

theorem main : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  intro D c v hc _ Gi j hj χS χT om hW F hF y hy
  exact ⟨vac_off hW hF (one_mem _) hy,
    (GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = Gi.q.v) (fun _ => False) (fun _ _ h => h)).2.2.1 χS χT om hW _
      (combAt_eg Gi j hj) 1 (one_mem _) y hy F hF.1⟩

end GlobalTheory.OffPlaceWeil
end

