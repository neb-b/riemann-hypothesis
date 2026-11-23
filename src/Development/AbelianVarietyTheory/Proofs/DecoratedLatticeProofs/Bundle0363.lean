module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnCondition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

section
variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem phit_mem_loc {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M := Iff.rfl

omit [StarRing E] in
theorem phit_mem_std {n : ℕ} (y : Fin n → E) :
    y ∈ Formalism.L2.Col.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [StarRing E] in
theorem phit_single_std {n : ℕ} (r : Fin n) : (Pi.single r 1 : Fin n → E) ∈ Formalism.L2.Col.stdLat E n := by
  rw [phit_mem_std]
  intro i
  by_cases h : i = r
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

omit [StarRing E] in
theorem phit_mk_ne (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem phit_local {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E) (hd : d.Ok) (hd' : d'.Ok)
    (hN : d.N = Formalism.L2.Col.stdLat E a) (hN' : d'.N = Formalism.L2.Col.stdLat E b) (P : ST)
    (hf : ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (hf' : ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (x : Formalism.L2.Col.HomE E a b) :
    (∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) ↔ ColCond P.1 t x := by
  haveI := P.1.isPrime
  have hle : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ d.at P.1 := fun y hy =>
    (phit_mem_loc P.1 _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.1.isPrime.ne_top, by rw [hN, one_smul]; exact hy⟩
  have hxs : ∀ (s : 𝓞 E) (y : Fin a → E), x (s • y) = s • x y := fun s y => x.map_smul_of_tower s y

  have hfe : ∀ r : Fin a, d.f P (Pi.single r 1) =
      Ideal.Quotient.mk P.1.asIdeal (t * if r.1 + 1 = a then 1 else 0) := by
    intro r
    have hr := r.2
    refine hf _ (phit_single_std r) ⟨a - 1, by omega⟩ (by simp only; omega) _ ?_
    by_cases h : r.1 + 1 = a
    · have : (⟨a - 1, by omega⟩ : Fin a) = r := Fin.ext (by simp only; omega)
      rw [this]; simp [h]
    · have : (⟨a - 1, by omega⟩ : Fin a) ≠ r := fun e => h (by have := congrArg Fin.val e; simp only at this; omega)
      simp [h, this]
  have hsm : ∀ (s : 𝓞 E) (z : Fin b → E) (q : Fin b), (s • z) q = algebraMap (𝓞 E) E s * z q := by
    intro s z q
    rw [Pi.smul_apply, Algebra.smul_def]
  constructor
  · intro h r
    obtain ⟨h1, h2⟩ := h _ (hle _ (phit_single_std r))
    obtain ⟨s, hs, hsx⟩ := (phit_mem_loc P.1 _ _).1 h1
    rw [hN'] at hsx
    choose c hc using (phit_mem_std _).1 hsx
    refine ⟨s, hs, c, fun q => by rw [hc, hsm], fun q hq => ?_⟩
    have e1 := hf' _ hsx q hq (c q) (hc q)
    rw [hd'.f_smul P s _ h1, h2, hfe, ← map_mul] at e1
    have e2 := Ideal.Quotient.eq.1 e1.symm
    convert e2 using 1
    split_ifs <;> ring
  · intro h
    have hb : b ≠ 0 := by
      rintro rfl
      obtain ⟨z, hz, hz0⟩ := hd'.f_ne P
      apply hz0
      have h0 := hd'.f_smul P 0 0 (Submodule.zero_mem _)
      rw [Subsingleton.elim z 0]
      simpa using h0
    let M : Submodule (𝓞 E) (Fin a → E) :=
      { carrier := {y | y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}
        add_mem' := by
          rintro y z ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
          refine ⟨Submodule.add_mem _ h1 k1, by rw [map_add (f := _)]; exact Submodule.add_mem _ h2 k2, ?_⟩
          rw [map_add (f := _), hd'.f_add P _ h2 _ k2, hd.f_add P _ h1 _ k1, h3, k3]
        zero_mem' := by
          refine ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
          have h0 := hd.f_smul P 0 0 (Submodule.zero_mem _)
          have h0' := hd'.f_smul P 0 0 (Submodule.zero_mem _)
          simp only [smul_zero, map_zero, zero_mul] at h0 h0'
          rw [map_zero, h0, h0']
        smul_mem' := by
          rintro s y ⟨h1, h2, h3⟩
          refine ⟨Submodule.smul_mem _ s h1, by rw [hxs]; exact Submodule.smul_mem _ s h2, ?_⟩
          rw [hxs, hd'.f_smul P s _ h2, hd.f_smul P s _ h1, h3] }
    have hM : ∀ y, y ∈ M ↔ (y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := fun _ => Iff.rfl
    have he : ∀ r : Fin a, (Pi.single r 1 : Fin a → E) ∈ M := by
      intro r
      obtain ⟨s, hs, c, hc, hq⟩ := h r
      have hsx : s • x (Pi.single r 1) ∈ Formalism.L2.Col.stdLat E b :=
        (phit_mem_std _).2 fun q => ⟨c q, by rw [hc, hsm]⟩
      have h1 : x (Pi.single r 1) ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2 ⟨s, hs, by rw [hN']; exact hsx⟩
      refine (hM _).2 ⟨hle _ (phit_single_std r), h1, ?_⟩
      have hq' : (⟨b - 1, by omega⟩ : Fin b).1 + 1 = b := by simp only; omega
      have e1 := hf' _ hsx _ hq' (c _) (by rw [hc, hsm])
      rw [hd'.f_smul P s _ h1] at e1
      apply mul_left_cancel₀ (phit_mk_ne P.1 hs)
      rw [e1, hfe, ← map_mul]
      refine Ideal.Quotient.eq.2 ?_
      convert hq _ hq' using 1
      split_ifs <;> ring
    have hstd : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ M := by
      intro y hy
      choose c hc using (phit_mem_std _).1 hy
      have : y = ∑ r, c r • (Pi.single r 1 : Fin a → E) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ← hc]
      rw [this]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (he r)
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (phit_mem_loc P.1 _ _).1 hy
    rw [hN] at hsy
    obtain ⟨-, h2, h3⟩ := (hM _).1 (hstd _ hsy)
    rw [hxs] at h2 h3
    obtain ⟨u, hu, huy⟩ := (phit_mem_loc P.1 _ _).1 h2
    have h1 : x y ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2
      ⟨u * s, fun hm => (P.1.isPrime.mem_or_mem hm).elim hu hs, by rw [mul_smul]; exact huy⟩
    refine ⟨h1, ?_⟩
    rw [hd'.f_smul P s _ h1, hd.f_smul P s _ hy] at h3
    exact mul_left_cancel₀ (phit_mk_ne P.1 hs) h3

end

theorem phiT_eq_one_iff_colCond : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  intro E _ _ _ a b ST SG SG' K _ d d' t hd hd' hN hN' hf hf' x
  classical
  unfold Formalism.L2.Col.phiT
  rw [ite_eq_left_iff]
  simp only [zero_ne_one, imp_false, not_not]
  exact forall_congr' fun P => phit_local d d' t hd hd' hN hN' P (hf P) (hf' P) x

end GlobalTheory.PhiOneVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealOcc

theorem pt_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T), ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
      R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hF i t
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  have hL : GlobalTheory.RawLift.Laws R F := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  obtain ⟨-, v, w, -, hne⟩ := GlobalTheory.RawLift.vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ
  refine ⟨v, w, fun h => hne ?_⟩
  unfold GlobalTheory.RawLift.jointVec GlobalTheory.RawLift.thetaIP
  rw [h]
  simp


set_option maxHeartbeats 1000000 in
theorem real_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t y hy m hm
  obtain ⟨v, w, hJ⟩ := pt_ne D G Pl0 T A Ks R F hG.core hF i t
  have hw : w ≠ 0 := by
    rintro rfl
    refine hJ ?_
    rw [map_zero]
    unfold RealDat.ptP
    exact map_zero _
  have H2 := _root_.GlobalTheory.Core.Rk.RealCoef.rcoef_scalar D G Pl0 T A Ks R F hG.core i t y m hm
  obtain ⟨z2, h2, h2ne⟩ := H2
  refine ⟨innerₛₗ ℂ w, R.ioP i (PiTensorProduct.tprod ℂ v) w, fun ν 𝓕 hν mR hmR => ?_⟩
  have H1 := _root_.GlobalTheory.WeilCoefScalar.wcoef_pure_eq_smul_inner D G Pl0 T A Ks R F hG.core hF i t v ν 𝓕 hν
  obtain ⟨z1, h1, h1ne⟩ := H1
  have e1 : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ :=
    fun b => h1 w b b.2
  have e : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b *
        GlobalTheory.Core.Rk.IP.rcoef m (fun g => innerₛₗ ℂ w (R.extV i t y g)) (fun g => innerₛₗ ℂ w (R.extV i t y g)) b =
      (z1 * z2) * ((‖⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun b => by
    calc _ = (z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ) * (z2 * ⟪(R.cV i).ρ (b : GA D (Vc D i)) w, w⟫_ℂ) :=
          congrArg₂ (· * ·) (e1 b) (h2 w b b.2)
      _ = _ := by
        rw [← inner_conj_symm ((R.cV i).ρ (b : GA D (Vc D i)) w) w, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_complex_ofReal]
  exact mul_ne_zero (mul_ne_zero (h1ne w hJ) (h2ne hy)) (Complex.ofReal_ne_zero.2
    (_root_.GlobalTheory.integral_normSq_coef_ne_zero D (Vc D i) (D.sp.V_sig _) (hG.core.models.vpos i) (R.cV i) (hG.core.models.cV i) w hw mR hmR))

end GlobalTheory.Core.Rk.RealOcc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.TailColumnRecursion

open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top

variable {D : D7}

theorem chain_cast {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C C' : ColumnChain R ι hc} (hC : C = C')
    (ψ : C.cls 0 → C.Y 0 → ℂ) (φ : C'.cls 0 → C'.Y 0 → ℂ) (h : HEq ψ φ) :
    (Eq.rec (motive := fun C _ => C.cls R.m → C.Y R.m → ℂ) (C.col ψ) hC) = C'.col φ := by
  subst hC; cases h; rfl

theorem rec_chain {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (ψ : C.cls 0 → C.Y 0 → ℂ) {a b : ℕ} (h : a = b) :
    Eq.rec (motive := fun n _ => C.cls n → C.Y n → ℂ) (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap a ψ) h = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap b ψ := by
  subst h; rfl

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem reads_uniq {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad)
    {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
    (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (jM : Pm.Mt →ₗ⋆[ℂ] Pm.Wrow)
    (hval : ∀ z ∈ M.ptC, ∀ c, eW z c ∈ LinearMap.range j)
    (hjM : ∀ F, jM F ∈ M.ptC) (hper : ∀ w F, Pm.period w F = M.ipP (jM F) w)
    (hpos : ∀ z ∈ M.ptC, M.ipP z z = 0 → z = 0)
    {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)}
    (h1 : ReadsG K eW j x G f) (h2 : ReadsG K eW j x G' f) : ∀ w, Pm.period w G = Pm.period w G' := by
  have hcard : ∀ c, (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := fun c => Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsingle : ∀ c v, Pm.period (eW.symm (Pi.single c (j v))) (G - G') = 0 := by
    intro c v
    obtain ⟨h, hh⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
    have a := (h1 c v h hh).symm.trans (h2 c v h hh)
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ (hcard c) a
  have hz : ∀ z ∈ M.ptC, Pm.period z (G - G') = 0 := by
    intro z hz
    have hdec : z = ∑ c, eW.symm (Pi.single c (eW z c)) := by
      apply eW.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single (eW z)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    obtain ⟨v, hv⟩ := hval z hz c
    rw [← hv]
    exact hsingle c v
  have hz0 : jM (G - G') = 0 := hpos _ (hjM _) (by rw [← hper]; exact hz _ (hjM _))
  intro w
  have := hper w (G - G')
  rw [hz0, map_zero, LinearMap.zero_apply, map_sub, sub_eq_zero] at this
  exact this

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem fic_val {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad) (lam : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1))
    {κ : Type} (yc : κ → Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (z : κ → FrP D → ℂ)
    (hz : z ∈ FiC S (Formalism.L2.Forms.embT D) lam yc) (c : κ) : z c ∈ ValC (gramC (gramP D) (Formalism.L2.Forms.embT D)) lam := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
  exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (yc c) (Set.mem_univ _)

theorem pos_core {κ : Type} [Fintype κ] {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (N : κ → ℕ) (hN : ∀ c, N c ≠ 0)
    (P : κ → MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (h : ∑ c, ((N c : ℕ) : ℂ)⁻¹ * Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c) = 0) : ∀ c, P c = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨c0, hc0⟩ := hne
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hterm : ∀ c, (((N c : ℕ) : ℂ)⁻¹ * Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re =
      ((N c : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re := by
    intro c
    rw [show ((N c : ℕ) : ℂ)⁻¹ = ((((N c : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  simp only [hterm] at hre
  have hnn : ∀ c, 0 ≤ ((N c : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re := by
    intro c
    refine mul_nonneg (by positivity) ?_
    by_cases hp : P c = 0
    · rw [hp]; simp [Formalism.MainNotions.product_first_zeroth_parts.nfAll, Formalism.REAL.fockF]
    · exact (GlobalTheory.LvT.PendExample.nfAll_pos lam hp).le
  have hpos : 0 < ((N c0 : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c0) (P c0)).re := by
    have : (0 : ℝ) < N c0 := by exact_mod_cast Nat.pos_of_ne_zero (hN c0)
    exact mul_pos (inv_pos.mpr this) (GlobalTheory.LvT.PendExample.nfAll_pos lam hc0)
  have := Finset.sum_pos' (fun c _ => hnn c) ⟨c0, Finset.mem_univ _, hpos⟩
  linarith

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

section G
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}


open Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw in
theorem eW_rep_G (V : ValuationAtPrimes K okW) (o : FrP D) (z : Pm.Wrow) (hz : z ∈ M.ptC) (c : M.clsP) :
    ∃ Q ∈ CSpan M.sg, V.eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := (V.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (K.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan M.sg := by
    have := CSpan_shW M.sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : V.eW z c = fnOf _ (shiftOf (sgTG M)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

theorem pos_G (V : ValuationAtPrimes K okW) : ∀ z ∈ M.ptC, M.ipP z z = 0 → z = 0 := by
  intro z hz h0
  obtain ⟨o, ho⟩ := GlobalTheory.PerRed.exists_orthonormal_frame₂ D
  choose P hP hPe using eW_rep_G V o z hz
  have hN : ∀ c, Nat.card (M.stabilizer₂ c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hPz := pos_core M.sg (fun c => Nat.card (M.stabilizer₂ c)) hN P ((V.ipP o ho z z P P hP hP hPe hPe).symm.trans h0)
  apply V.eW.injective
  rw [map_zero]
  funext c
  rw [hPe c, hPz c, map_zero]
  rfl

end G

theorem pos_0 {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    ∀ z ∈ (D.fm u).ptC, (D.fm u).ipP z z = 0 → z = 0 := by
  intro z hz h0
  obtain ⟨o, ho⟩ := GlobalTheory.PerRed.exists_orthonormal_frame₂ D
  choose P hP hPe using GlobalTheory.PerRed.eW_rep_o T o z hz
  have hN : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hPz := pos_core (D.fm u).sg (fun c => Nat.card ((D.fm u).stabilizer₂ c)) hN P
    ((T.valP.ipP o ho z z P P hP hP hPe hPe).symm.trans h0)
  apply T.valP.eW.injective
  rw [map_zero]
  funext c
  rw [hPe c, hPz c, map_zero]
  rfl

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem domWeight_ext {n : ℕ} : ∀ a b : DomWeight n, a.w = b.w → a = b := by
  rintro ⟨a, _⟩ ⟨b, _⟩ h; cases h; rfl

theorem sg_eq {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (V : ValuationAtPrimes K okW) {K0 : ClsPTied u} (V0 : ValPTied u K0) : sgTG M = sgT u := by
  funext τ
  unfold sgTG sgT
  congr 1
  apply domWeight_ext
  funext i
  have a := V.sg τ i
  have b := V0.sg τ i
  exact_mod_cast a.trans b.symm

theorem referenceTuple_familyPeriod_eq_period (u : D.what₂.Word) (μ : D.what₂.Tup) (h0 : μ = D.what₂.mu0)
    (ψ0 : (D.chTw u μ).cls 0 → (D.chTw u μ).Y 0 → ℂ) (φ : D.what₂.Mu u) (hφ : HEq ψ0 (D.eMu u φ).1)
    (G1 G0 : D.what₂.Amb μ)
    (hu : ∀ w, (D.mem u).P.period w ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G1 h0)) =
      (D.mem u).P.period w ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G0 h0))) :
    (D.mem u).P.Ptil (Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ)
        (Eq.rec (motive := fun ν _ => (D.chTw u ν).cls D.R.m → (D.chTw u ν).Y D.R.m → ℂ) ((D.chTw u μ).col ψ0) h0)
        (D.memberColumns_twistedChain_base u))
      ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G1 h0)) = D.what₂.perCol u μ φ G0 := by
  subst h0
  rw [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
  simp only at hu ⊢
  rw [hu, chain_cast (D.memberColumns_twistedChain_base u) ψ0 _ hφ]

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop
open Classical
open GlobalTheory.MiTop.TailColumnRecursion Formalism.L2.Forms

end GlobalTheory.MiTop

end
end

