module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MeasRd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def ratAt : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)

def ExactAt : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
    nrmR p.R.toRealDat i σ ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
      Real.sqrt (ratAt p i) * petW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
        (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) f

theorem measAt_of (h : ExactAt p i) (hr : 0 < ratAt p i) {K₁ K₂ : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂)
    (hu : Real.log (ratAt p i) ≤ K₁ * unitE p) (hl : -(K₂ * unitE p) ≤ Real.log (ratAt p i)) :
    MeasAt p i ((K₁ + K₂) / 2) := by
  intro σ
  refine ⟨Real.sqrt (ratAt p i), Real.sqrt_pos.2 hr, ?_, fun f => h σ f⟩
  rw [Real.log_sqrt hr.le]
  have key : |Real.log (ratAt p i)| ≤ (K₁ + K₂) * unitE p := by
    rcases le_or_gt 0 (unitE p) with hu0 | hu0
    · rw [abs_le]; constructor <;> nlinarith
    · have hs : K₁ + K₂ = 0 := by nlinarith
      have e1 : K₁ = 0 := by linarith
      have e2 : K₂ = 0 := by linarith
      subst e1 e2
      have : Real.log (ratAt p i) = 0 := by
        apply le_antisymm <;> simp_all
      rw [this, hs]; simp
  rw [abs_div, abs_two]
  have : |Real.log (ratAt p i)| / 2 ≤ (K₁ + K₂) * unitE p / 2 := by linarith
  linarith [this, show (K₁ + K₂) * unitE p / 2 = (K₁ + K₂) / 2 * unitE p by ring]

end GlobalTheory.CovTop.MeasRd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInte
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.QHalfLat

variable {D : D7}
open scoped Matrix

theorem frMapAdj_gen {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} {α : Af D.host.F}
    (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (hca : toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hca hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fS hs) (GlobalTheory.ConjHalfInt.pair_row_int hT fT ht)

theorem isIntM_adj_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} (hc : ∀ a ∈ D.host.AA, toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {x : WO S T} (hx : IsHalf c x)
    (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapAdj S T βS βT x) := by
  have hx' : c • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (c • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact frMapAdj_gen hS hT fS fT hα' (hc a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem placesOK_of {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    (hQ : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : GlobalTheory.ExportSeries.PlacesOK Q ∅ := by
  refine ⟨⟨Q, subset_rfl, Finset.empty_subset _, (⟨e, he⟩ : ∃ e : AE D, IsIdemSum e Q)⟩, Finset.disjoint_empty_right _, ?_⟩
  rintro PP (hPP | hPP) PP' hPP'
  · rcases hPP' with rfl | hc
    · exact GlobalTheory.HalfCompare.primeToAA_of_not_mem (hQ _ hPP)
    · rw [(GlobalTheory.IdemSupport.isConjPl_iff PP PP').1 hc]
      refine GlobalTheory.HalfCompare.primeToAA_of_not_mem ?_
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hQ PP hPP
  · simp at hPP

end GlobalTheory.QHalfLat


open GlobalTheory.QHalfLat in
theorem GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQt eQ he t ht
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, ht0⟩ := hQt
  have hbad : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t0 PP (ht0 hPP)
  have hP := placesOK_of he hbad
  have hid : GlobalTheory.ExportSeries.idem Q = eQ :=
    GlobalTheory.DatumFourier.idemSum_unique (Vc D i) he (show GlobalTheory.ExportSeries.SplitSet Q from ⟨eQ, he⟩).isIdemSum
  have ht' : IsHalf (cA D (GlobalTheory.ExportSeries.idem Q)) t := by rw [hid]; exact ht
  constructor
  · intro hi
    exact GlobalTheory.ConjLatAdj.mem_latO_of_adj_int hSV hSW hFV hFW hP ht' hi
  · intro hl
    exact isIntM_adj_of_mem hSV hSW hFV hFW (fun a ha => GlobalTheory.ConjHalfInt.toEAf_cA_idem_mul_mem hP ha) ht' hl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLatInt

variable {D : D7}

theorem toEAf_idem_mul_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {a : D.host.E}
    (ha : a ∈ D.host.AA) : toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  exact GlobalTheory.ConjHalfInt.toEAf_mul_mem ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))
    (GlobalTheory.HalfCompare.primeToAA_of_not_mem (hP PP hPP)) ha

theorem isIntM_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapO S T βS βT x) := by
  have hx' : e • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO S T βS βT (e • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      unfold frMapO
      rw [GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (βT⁻¹).val, Matrix.mul_assoc]
      exact GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_idem_mul_mem he hP ha) hα')
        (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fT ht)
          (GlobalTheory.ConjHalfInt.pair_row_int hS fS hs))
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
    exact fun i j => neg_mem (hu i j)


open GlobalTheory.ExportSeries.Model in
theorem isIntM_adj {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {x : WO S T} (h : IsIntM (frMapO S T βS βT x)) : IsIntM (frMapAdj S T βS βT x) := by
  have e : x.map (toEAf D) = βT.val * frMapO S T βS βT x * (βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hS fS).2 (int_ct h)) (gram_frame_int T hT fT).1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

theorem mem_of_isIntM {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (h : IsIntM (frMapO S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  refine GlobalTheory.DatumFourier.mem_latO_of_int hS hT fS fT (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj he) hN
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) ?_ ?_ (isIntM_adj hS hT fS fT h)
  · intro PP' hPP' hm
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hPP'
    have h2 : Formalism.L2.DIV.starOHom ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hm
    rw [map_natCast] at h2
    exact hP PP hPP (GlobalTheory.HalfCompare.mem_of_dvd h2 (Dvd.intro_left _ rfl))
  · intro i j
    rw [Formalism.L2.Theta.cA_cA]
    exact hx i j

end GlobalTheory.HalfLatInt

theorem GlobalTheory.HalfLatInt.isIntM_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQ eQ he x hx
  obtain ⟨t, hQt⟩ := hQ
  have hSV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hP : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t PP (hQt hPP)
  exact ⟨GlobalTheory.HalfLatInt.mem_of_isIntM hSV hSW hBV.1 hBW.1 he hP hx,
    GlobalTheory.HalfLatInt.isIntM_of_mem hSV hBV.1 hBW.1 he hP hx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModifResidueFieldMapSurjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
open GlobalTheory.Vanishing.H0 GlobalTheory.CompHS

namespace GlobalTheory.HSApp

theorem modif_generic_map {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IrreducibleSpace M.X] (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    genericPoint M.X ∈ M.opn ∧ M.σ (genericPoint M.X) = η := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hm : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  refine ⟨hm, ?_⟩
  obtain ⟨x, hx⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hx' : M.σ x.1 = η := (morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)
  have hcl : η ∈ closure {M.σ (genericPoint M.X)} := by
    rw [← hx', ← Set.image_singleton]
    exact image_closure_subset_closure_image M.σ.continuous
      ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩
  have hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
  exact hgen.eq hg

theorem modif_residueFieldMap_surjective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) (z : M.X) (hz : z ∈ M.opn) : Function.Surjective (M.σ.residueFieldMap z).hom := by
  have := M.iso
  have : IsIso (M.σ.stalkMap z) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1
      (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)
  have hst : Function.Surjective (M.σ.stalkMap z).hom := (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨a, rfl⟩ := M.X.residue_surjective z y
  obtain ⟨b, rfl⟩ := hst a
  exact ⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩

theorem modif_residueFieldMap_germ {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    (hnb : NoBase hB W U) (z : M.X) (hz : z ∈ M.opn) (i : B.ι) (hi : M.σ z ∈ B.U i) :
    ∃ c : M.X.residueField z, c ≠ 0 ∧ ∀ w : W,
      (M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (germ i (M.σ z) (memTop _) hi w.1)) =
        c * (M.sys Δ φ f abelian₂).toLinSys.val (Adelic.resPt z) (toSec (Δ.lift w)) := by
  set S := (M.sys Δ φ f abelian₂).toLinSys
  have hp : Adelic.ptOf (Adelic.resPt z) = z := Adelic.ptOf_resPt z
  have hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z))) :=
    (congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp
      (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))
  set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))
  have hi0 : M.σ z ∈ B.U (j.1 PUnit.unit) := mem_pull.1 hj.1
  have hu : IsUnit (ger z hj.2 (Δ.t.f j.2)) :=
    (isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))
  refine ⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) *
    (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩
  · exact (map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)
  · exact (hu.map (M.X.residue z).hom).ne_zero
  have hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w)) := by
    rw [Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]
    rfl
  rw [hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]
  congr 1
  rw [← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]
  refine Eq.trans ?_ (congrArg (M.X.residue z).hom
    (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm
  exact congr($(Scheme.residue_residueFieldMap M.σ z).hom _)

theorem sys_birational_of_ratField {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    [IsIntegral M.X] (hnb : NoBase hB W U) (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ)
    (hr : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) η hη = ⊤) :
    (M.sys Δ φ f abelian₂).toLinSys.Birational := by
  classical
  obtain ⟨hmem, hσ⟩ := modif_generic_map M η hη hg
  subst hσ
  set S := (M.sys Δ φ f abelian₂).toLinSys with hS
  set z := genericPoint M.X with hz
  have hsurj := modif_residueFieldMap_surjective M z hmem
  have hbpf : S.BasePointFree := Δ.iSup_nonzeroLocus (f.b.map φ).span_eq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))
  have key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈
      S.ratioField (Adelic.resPt z) := fun w => by
    set u := f.b.equivFun (φ.symm w)
    have e : toSec (Δ.lift w) = S.comb u := by
      refine (bijective_ofSec_top (p := M.str)).1 ?_
      rw [ofSec_toSec]
      refine Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm
      simp [u]
    rw [e, S.val_comb, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))
  have hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U),
      s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s')},
      (M.σ.residueFieldMap z).hom r ∈ S.ratioField (Adelic.resPt z) := by
    rintro r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩
    obtain ⟨c, hc, hcw⟩ := modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi
    rw [germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc,
      ← div_div_div_cancel_right₀ hj0]
    exact div_mem (key w) (key w')
  have hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤
      (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom :=
    Subfield.closure_le.2 hgen
  refine ⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hr.symm ▸ Subfield.mem_top y)

theorem geo_second_birational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₂ → (h.geo f₁ f₂ th k).second.Birational := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  have : IsIntegral R.X := (h.geo f₁ f₂ th k).isIntegral
  refine sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_
  convert hrat using 2
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtInfinitySetStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_infinity_set : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, (mat g * γ * Matrix.transpose (mat h) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∃ c : ℂ, om' (g, h) (pure f φ) = c • pure f φ := by
  first | exact @GlobalTheory.VacScalar.scalar_of_trivial | exact GlobalTheory.VacScalar.scalar_of_trivial | (intros; apply GlobalTheory.VacScalar.scalar_of_trivial <;> assumption)
end

