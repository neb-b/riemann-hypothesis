module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0616

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem intAf_mul' {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem pairA_mul' (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl

theorem mul_ePl {v : GlobalTheory.FinPl.Pl D} {α : Af D.host.F} (h : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * GlobalTheory.FinPlLoc.ePl D (· = v) = α := by
  classical
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (α * _) = evalV D.host.F w α
  rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · rw [if_pos hw, mul_one]
  · rw [if_neg hw, mul_zero, h w hw]

theorem smul_mem_homLat {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    {c : D.host.E} (hc : c ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹)
    {X : Matrix (Fin m) (Fin n) D.host.E} (hX : X ∈ 𝔪 • homLat Λ Λ') : c • X ∈ homLat Λ Λ' := by
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun x y hx hy => ?_)
  · have h1 : c * algebraMap (𝓞 D.host.E) D.host.E r ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hne]
      exact FractionalIdeal.mul_mem_mul hc (FractionalIdeal.mem_coeIdeal_of_mem _ hr)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have e : c • (r • Y) = o • Y := by
      rw [← algebraMap_smul D.host.E r Y, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact Submodule.smul_mem _ o hY
  · rw [smul_add]; exact add_mem hx hy

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {v : GlobalTheory.FinPl.Pl D}
    {z : AE D} (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) {x : Mx D m n}
    (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : z • x ∈ hatMx (homLat Λ Λ') := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, X, hX, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨α * β, intAf_mul' hα hβ, c • X, smul_mem_homLat h𝔪 hc hX, ?_⟩
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul']
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha

theorem val_le_one_of_mem_inv {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {a : D.host.E} (ha : a ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹) :
    Valued.v (algebraMap D.host.E (Kw Q) a) ≤ 1 := by
  obtain ⟨m, hm, hmQ⟩ := Set.not_subset.1 hQ
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h1 : a * algebraMap (𝓞 D.host.E) D.host.E m ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [← inv_mul_cancel₀ hne]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  rw [show Valued.v (algebraMap D.host.E (Kw Q) a) = Q.valuation D.host.E a from
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q a]
  have hm1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E m) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (Q.intValuation_le_one m)
      (not_lt.1 fun h => hmQ ((Q.intValuation_lt_one_iff_mem m).1 h))
  have ho1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤ 1 := Q.valuation_le_one o
  rw [ho, map_mul, hm1, mul_one] at ho1
  exact ho1

end GlobalTheory.DepthMap

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem val_cpt_le_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {v : GlobalTheory.FinPl.Pl D} {z : AE D}
    (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) :
    Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D z)) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    have e : pairA D.host.F 0 α ⊗ₜ[D.host.F] c =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c := by
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      show GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (incA D c)) = algebraMap D.host.E (Kw Q) c from Comparison₂.cpt_tmul Q c]
    have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
    exact mul_le_one' (((GlobalTheory.StdFrames.comp_toAd D).int _).1 hi Q) (val_le_one_of_mem_inv h𝔪 hQ hc)
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]; exact Valuation.map_add_le _ hx hy
  | neg x _ hx => rw [RingHom.map_neg, RingHom.map_neg, Valuation.map_neg]; exact hx

theorem cpt_idemSum_of_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P, Finset.sum_eq_single Q]
  · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
  · intro b hb hbQ; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q (Ne.symm hbQ)
  · intro h; exact absurd hQ h

theorem cpt_idemSum_of_not_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∉ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P]
  exact Finset.sum_eq_zero fun b hb => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q fun h => hQ (h ▸ hb)

theorem modul_not_le {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : Q ∉ P.W0) : ¬ P.modul sc ≤ Q.asIdeal := by
  classical
  intro h
  unfold Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le hle
  have h2 : P.w v = Q := HeightOneSpectrum.ext ((P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1)
  exact hQ (h2 ▸ Finset.mem_image_of_mem P.w hv)

end GlobalTheory.DepthMap


open GlobalTheory.DepthMap in
theorem GlobalTheory.DepthMap.smul_mulVec_mem_latV : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  intro D hD T L μ0 hL sc G W M hM i hi u hu v hv y hy s hs
  classical
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  have P7 := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hm0 : G.pl.modul sc ≠ ⊥ := G.pl.modul_ne_bot sc
  have hmF : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hm0
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨-, -, -, -, -, P6, P7'⟩ := P7
  have key : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
        (G.Λ (.grid i 0) : Set _) (· = v) := by
    intro z hz
    obtain ⟨g, hg, g', hg', hid, hiff⟩ := P6 _ (inv_ne_zero hmF)
    have hzA : z ∈ idAt D (· = v) := ((hiff z).1 hz).1
    have hsplit : z • u = (e * z) • u + ((1 - e) * z) • u := by
      rw [← add_smul]; congr 1; ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
      have h2 := smul_mem_hatMx hm0 hz h1
      have h3 : (e * z) • u = z • (e • u) := by rw [mul_comm, mul_smul]
      rw [h3]
      have hhalf : IsHalf e (z • (e • u)) := fun a b => by
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_comm e z, mul_assoc, ← mul_assoc e e, GlobalTheory.PlaceDatum.idemSum_mul_self he]
      have h4 := GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hD hL G) hhalf h2
      refine (GlobalTheory.AscFinWit.mem_latO_at (fun a b => ?_)).1 h4
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hzA
    · have hint : finPart D ((1 - e) * z) ∈ intAE D := by
        refine ((GlobalTheory.StdFrames.comp_toAd D).int _).2 fun Q => ?_
        show Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D ((1 - e) * z))) ≤ 1
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
        by_cases hQ : Q ∈ G.pl.W0
        · rw [cpt_idemSum_of_mem he hQ, sub_self, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hc := cpt_idemSum_of_not_mem he hQ
          have hb := val_cpt_le_one hm0 (modul_not_le G.pl sc hQ) hz
          simp only [hc, sub_zero, one_mul]
          exact hb
      have hI : (1 - e) * z ∈ intAt D (· = v) := by
        refine ⟨?_, hint⟩
        exact Ideal.mul_mem_left _ _ hzA
      have hS := GlobalTheory.RowInt.smul_mem_latO_at D hD T L μ0 hL sc G W M hM
      exact hS i hi v _ hI u hu
  have hlatA : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • (u *ᵥ y) ∈ latA (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
    intro z hz
    rw [← Matrix.smul_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hsd (key z hz) hy
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, hsupp, a, ha, rfl⟩ := hs
    refine FractionalIdeal.mul_induction_on
      (C := fun a => (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) • (u *ᵥ y) ∈
        GlobalTheory.FinPl.latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v)) ha (fun b hb c hc => ?_)
      (fun x x' hx hx' => ?_)
    · have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] b) *
          (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul', mul_ePl hsupp]
      have hz : pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c ∈
          GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v :=
        AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPlLoc.ePl_int _, fun w hw => by
          rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw], c, hc, rfl⟩
      have hs' : pairA D.host.F 0 α ⊗ₜ[D.host.F] b ∈ GlobalTheory.SeeSaw.idV D.host.AA⁻¹ v :=
        AddSubgroup.subset_closure ⟨α, hα, hsupp, b, hb, rfl⟩
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c)) • (u *ᵥ y) ∈ _
      rw [e1, mul_smul]
      exact ((P7' _ _ _).1 (hlatA _ hz)).2 _ hs'
    · show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x + x')) • (u *ᵥ y) ∈ _
      rw [TensorProduct.tmul_add, add_smul]; exact add_mem hx hx'
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TflipField

section Generic

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]


omit [MeasurableSpace k] [BorelSpace k] in
theorem apow_nat_half_mem (F : Subfield ℂ) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (x : kˣ) (n : ℕ) :
    apow x ((n : ℂ) / 2) ∈ F := by
  have : apow x ((n : ℂ) / 2) = apow x (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]; exact F.pow_mem (habs x) n


omit [MeasurableSpace k] [BorelSpace k] in
theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y ∈ F := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine F.mul_mem (F.inv_mem (F.pow_mem (natCast_mem F _) _)) (F.sum_mem fun T _ => F.mul_mem (hΦ _) (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact F.zero_mem


omit [MeasurableSpace k] [BorelSpace k] in
theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Φ T ∈ F := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine F.sum_mem fun S _ => F.mul_mem (hΦ _) (hψ _ ?_)
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact F.zero_mem

theorem smallF_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (h : GL D k) :
    smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F :=
  _root_.GlobalTheory.SmallFInF.smallF_mem F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF h

theorem phiA_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) (Λ' : Submodule 𝒪[k] (D → k))
    {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (X : Matrix A D k) :
    phiA (haarVol J) σ ν ϖ e Λ' Ψ X ∈ F := by
  classical
  unfold phiA
  split_ifs
  · unfold fFun
    split_ifs with hX
    · exact F.mul_mem (F.mul_mem (hνF _) (apow_nat_half_mem F habs _ _))
        (smallF_mem F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF _)
    · exact F.zero_mem
  · exact F.zero_mem

theorem flipTensor_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) {i j : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνF : ∀ u, (G.nu i j u : ℂ) ∈ F) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (hTF : ∀ x, T x ∈ F)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j J T x ∈ F := by
  have hJ' := isOpen_map_invT hJ hK
  unfold Grid.flipTensor squareFlip
  exact invFourierSum_inv_mem F ψ ϖ e _ hψ (fun X => phiA_mem F hJ'.1 hJ'.2 _ _ hϖ he hν hram hνF habs
    (blockUnits ϖ e _) _ ((FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ (isNatDatum_sliceB hT h1 h2 x))
    (fun Y => fourierSum_mem F ψ ϖ e _ hψ (fun Z => hTF _) Y) X) _

theorem flips_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ ∀ u, (G.nu x.1 x.2 u : ℂ) ∈ F) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, S.tensor z ∈ F) → ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ F := by
  intro l
  induction l with
  | nil => intro S _ _ _ _ hF; exact hF
  | cons x l ih =>
    intro S hν hc hJ hT hF
    obtain _ | ⟨hp, hc'⟩ := hc
    have hsub := hp.subset
    have hx := hν x List.mem_cons_self
    refine ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (isTensor_flipTensor hϖ hψc he hx.1 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT)
      (flipTensor_mem F hϖ hψc he habs hψ hx.1 hx.2.1 hx.2.2 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT hF)
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end Generic

end GlobalTheory.TflipField

namespace GlobalTheory.TflipField

section Concrete

open ValuativeRel Formalism.L2.Host

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem givenStage_mem (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
    (z : (locGrid G t w).Args) : (givenStage t w B Φ).tensor z ∈ F :=
  _root_.GlobalTheory.GivenField.tensor_givenStage_mem F B t Φ w hmu hxi z

theorem nu_mem (F : Subfield ℂ) (t : T) (w : Pl D.host.E) (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F)
    (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((G.ch.chiH i).loc w x : ℂ) ∈ F)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : ((locGrid G t w).nu i j u : ℂ) ∈ F := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact F.mul_mem (F.mul_mem (hmu _ _) (hxi _)) (F.inv_mem (hchi _ (by omega) (by omega) _))

theorem psiAt_mem (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}
    (hroots : ∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) (hcond : HasConductor (psiAt W w) 1)
    (x : Kw w) (hx : valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ∈ F :=
  _root_.GlobalTheory.FunObj.psiAt_mem_subfield_of_roots F hroots hcond x hx

theorem apow_half_mem (F : Subfield ℂ) (w : Pl D.host.E)
    (hsq : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F) (u : (Kw w)ˣ) : apow u (1 / 2) ∈ F :=
  _root_.GlobalTheory.HalfPowField.apow_half_mem_of_sqrt F w hsq u

end Concrete

end GlobalTheory.TflipField

namespace GlobalTheory.RowTest

theorem Tflip_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D)
    (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum),
    ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ hF t Φ _ w hw z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) ∧ ∀ u, ((locGrid ch.G t w).nu x.1 x.2 u : ℂ) ∈ K := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    refine ⟨by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi hi hj⟩
  have key := GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
    (givenStage t w ch.S.B Φ) hν (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
    (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z
  exact RingHom.mem_fieldRange.1 key

end GlobalTheory.RowTest
end
end

