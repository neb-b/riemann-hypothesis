module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodular
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.HeisTranslate

theorem mem_of_inc_mem_hatId {D : D7} {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {e : D.host.E}
    (he : inc D e ∈ hatId D J) : e ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have hJ0 : (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    simpa using hJ
  have key : ∀ y ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹, ∀ w ∈ hatId D J, w * inc D y ∈ OhE D := by
    intro y hy w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, s, hs, rfl⟩ := hz
      have hby : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [← mul_inv_cancel₀ hJ0]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hby
      have e1 : inc D (b : D.host.E) * s * inc D y = inc D ((c : 𝓞 D.host.E) : D.host.E) * s := by
        rw [show ((c : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E c from rfl, hc, map_mul]
        ring
      rw [e1]
      exact mul_mem (VacMove.inc_int D c) hs
    | zero => simpa using (OhE D).zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  rw [← inv_inv (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), FractionalIdeal.inv_eq,
    FractionalIdeal.mem_div_iff_of_ne_zero (inv_ne_zero hJ0)]
  intro y hy
  rw [FractionalIdeal.mem_one_iff]
  have hint : e * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.E _ fun v => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, map_mul]
    exact GlobalTheory.Mem.Col2.SplitChar.vl_le (key y hy _ he) v
  exact hint

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem pt_mem_La_skew {D : D7} (δ : ℂ) (𝔫 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E)
    (hz : ∀ i j, z i j ∈ (((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d) := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have hx' : ∀ j, x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := fun j => by
      simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hx
      exact hx j
    show ∑ j, z i j * x j ∈ _
    refine sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx' j)
    rw [← hc, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c (hz i j)

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    Hf D T b a = starRingEnd ℂ (Hf D T a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_wdPh (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖wdPh D T x‖ = 1 := by
  simp [wdPh, ee, Complex.norm_exp]

theorem wd_wd_unimod (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · have hre : ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2).re = 0 := by
      rw [hf_swap D T a b]
      simp [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [norm_mul, norm_div, norm_mul, norm_wdPh, norm_wdPh, norm_wdPh, Complex.norm_exp, hre]
    simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem wd_unitVec_congr : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, inc D (y i l - y' i l) ∈ hatId D (D.host.conj • 𝔪)) → ∃ c : ℂ, ‖c‖ = 1 ∧ Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho y y' hyy
  have hm' : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨g', x', -, hg'm, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) hm' hcop' d
  have hsd : SD D (skewLat D (D.host.conj • 𝔪) d) := VacMove.sd_of_moves hg'm
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hF := GlobalTheory.SkewTheta.iop_mem_thSp D δ hc e0 hv.1 (D.host.conj • 𝔪) hsd
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hne : ((D.host.conj • D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [hcc]; simpa using hm
  have hx : pt D (tor0 D ⊤ δ) δ (y - y') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d) := by
    refine pt_mem_La_skew δ (D.host.conj • 𝔪) (y - y') fun i j => ?_
    have hmem := mem_of_inc_mem_hatId hm' (hyy i j)
    rw [Matrix.sub_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hne]
    intro w hw
    obtain ⟨c, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hmem
  have hfix := VacMove.wd_fix h1 hc hK hF hx
  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_unimod D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (pt D (tor0 D ⊤ δ) δ (y - y'))
  have e := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d)
    (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)
  rw [hfix, ← VacMove.pt_add, add_sub_cancel] at e
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ1; exact zero_ne_one hφ1
  refine ⟨φ⁻¹, by rw [norm_inv, hφ1, inv_one], ?_⟩
  rw [e, smul_smul, inv_mul_cancel₀ hφ0, one_smul]

end GlobalTheory.HeisTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open MeasureTheory
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriMove

variable {D : D7}

def rdx {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin m) (Fin n) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix id (finCongr h).symm

def rdi {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix (finCongr h).symm id

theorem rdx_rdi {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdx (K := K) h * rdi (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

theorem rdi_rdx {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdi (K := K) h * rdx (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

def glMove {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : GL (Fin m) K) : GL (Fin n) K where
  val := HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h)
  inv := HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q
  val_inv := by
    have e1 := rdx_rdi (K := K) h
    have e2 : (x.1 : Matrix (Fin m) (Fin m) K) * x.2 = 1 := x.val_inv
    calc HMul.hMul (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
          (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
        = HMul.hMul (HMul.hMul P (HMul.hMul (HMul.hMul (x.1 : Matrix (Fin m) (Fin m) K) (HMul.hMul (rdx (K := K) h) (rdi (K := K) h))) (x.2 : Matrix (Fin m) (Fin m) K))) Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, PQ]
  inv_val := by
    have e1 := rdi_rdx (K := K) h
    have e2 : (x.2 : Matrix (Fin m) (Fin m) K) * x.1 = 1 := x.inv_val
    calc HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
          (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
        = HMul.hMul (HMul.hMul (rdi (K := K) h) (HMul.hMul (HMul.hMul (x.2 : Matrix (Fin m) (Fin m) K) (HMul.hMul Q P)) (x.1 : Matrix (Fin m) (Fin m) K))) (rdx (K := K) h) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [QP, Matrix.mul_one, e2, Matrix.mul_one, e1]

variable {S S' T T' : HSp D}

def fP (I : IsoMat S S') : Matrix (Fin S'.rank) (Fin S.rank) (Lev.EAf D) := I.P.map (eToEAf D)

def fQ (I : IsoMat S S') : Matrix (Fin S.rank) (Fin S'.rank) (Lev.EAf D) := I.Q.map (eToEAf D)

theorem fP_fQ (I : IsoMat S S') : fP I * fQ I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fQ_fP (I : IsoMat S S') : fQ I * fP I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.QP, Matrix.map_one _ (map_zero _) (map_one _)]

def betaMove (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) : GL (Fin S'.rank) (Lev.EAf D) :=
  glMove I.rank_eq (fP I) (fQ I) (fP_fQ I) (fQ_fP I) β

def latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E) :=
  Λ.map ((Matrix.mulVecLin I.P).restrictScalars (𝓞 D.host.E))

def cartMove (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * s * I.qT τ

def basMove (I : IsoMat S S') (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * B * rdx I.rank_eq

def rigMove (I : IsoMat S S') (r : Rig S) : Rig S' where
  Λ := latMove I r.Λ
  β := betaMove I r.β
  s τ := cartMove I τ (r.s τ)
  B τ := basMove I τ (r.B τ)

def homMap (IS : IsoMat S S') (IT : IsoMat T T') : WO S T ≃+ WO S' T' where
  toFun x := HMul.hMul (HMul.hMul IT.aP x) IS.aQ
  invFun y := HMul.hMul (HMul.hMul IT.aQ y) IS.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul IT.aQ (HMul.hMul (HMul.hMul IT.aP x) IS.aQ)) IS.aP = x
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aQ IT.aP) x) (HMul.hMul IS.aQ IS.aP) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [IT.aQ_aP, IS.aQ_aP, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul IT.aP (HMul.hMul (HMul.hMul IT.aQ y) IS.aP)) IS.aQ = y
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aP IT.aQ) y) (HMul.hMul IS.aP IS.aQ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [IT.aP_aQ, IS.aP_aQ, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    show HMul.hMul (HMul.hMul IT.aP (x + y)) IS.aQ = HMul.hMul (HMul.hMul IT.aP x) IS.aQ + HMul.hMul (HMul.hMul IT.aP y) IS.aQ
    rw [Matrix.mul_add, Matrix.add_mul]

theorem homMap_apply (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS IT x = HMul.hMul (HMul.hMul IT.aP x) IS.aQ := rfl

def trH (IS : IsoMat S S') (IT : IsoMat T T') (f : WO S T → ℂ) : WO S' T' → ℂ := fun w => f ((homMap IS IT).symm w)

def trLE (IS : IsoMat S S') (IT : IsoMat T T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (homMap IS IT).symm.toEquiv

def omH (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) :=
  (trLE IS IT).conjRingEquiv.toMulEquiv.toMonoidHom.comp (om.comp (IS.kap.symm.toMonoidHom.prodMap IT.kap.symm.toMonoidHom))

theorem omH_apply (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S') (h : GA D T') (f : WO S' T' → ℂ) :
    omH IS IT om (g, h) f = trH IS IT (om (IS.kap.symm g, IT.kap.symm h) (trH IS.symm IT.symm f)) := rfl

def polMove {m n m' n' : ℕ} (hm : m = m') (hn : n = n') :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m' n') ℂ :=
  MvPolynomial.rename fun k => (k.1, finCongr hm k.2.1, finCongr hn k.2.2)

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

def triMove (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) : Tri T₀ A A' WW where
  rA := rigMove IA Y.rA
  rA' := rigMove IA' Y.rA'
  rW := rigMove IW Y.rW
  ω t := omH IA IW (Y.ω t)
  ω' t := omH IA' IW (Y.ω' t)
  vac := trH IA IW Y.vac
  vac' := trH IA' IW Y.vac'
  e := Y.e
  c := Y.c
  f t := trH IA IW (Y.f t)
  f' t := trH IA' IW (Y.f' t)
  m := Y.m.map IA.kap
  fd := IA.kap.symm ⁻¹' Y.fd
  m' := Y.m'.map IA'.kap
  fd' := IA'.kap.symm ⁻¹' Y.fd'

end GlobalTheory.TriMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvd
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemOrth

theorem idemAt_orth {D : D7} {a b : AE D} {i j : Formalism.L2.DIV.Pl D.host.E} {n : ℕ} (ha : Formalism.L2.NTheta.IsIdemAt a i)
    (hb : Formalism.L2.NTheta.IsIdemAt b j) (hi : ((n : ℕ) : 𝓞 D.host.E) ∈ i.asIdeal)
    (hj : ((n : ℕ) : 𝓞 D.host.E) ∉ j.asIdeal) : (a + cA D a) * (b + cA D b) = 0 := by
  obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, a4⟩ := ha
  obtain ⟨⟨b1, b2, v', ε', hε', b3⟩, b4⟩ := hb
  by_cases hv : v = v'
  · exfalso
    rw [← hv] at hε'
    have hab : a + cA D a = b + cA D b := a3.trans (GlobalTheory.PlaceDatum.placeIdem_eq hε hε' ▸ b3.symm)
    have hn : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hj (h ▸ zero_mem _)
    have h1 := not_not.1 (mt (b4 _ hn).2 hj)
    have h2 := GlobalTheory.MovedIdem.finPart_conj_mem h1
    have hs : star ((((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) = (((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_natCast (R := D.host.E) n
    rw [hs] at h2
    have h3 := not_not.1 (mt (a4 1 one_ne_zero).2 ((Ideal.ne_top_iff_one _).1 i.isPrime.ne_top))
    have h4 : incA D (((1 : 𝓞 D.host.E) : D.host.E)⁻¹) = 1 := by
      rw [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one]
    rw [h4, mul_one] at h3
    have h5 := GlobalTheory.SplitLatBasis.mul_mem_intAE D h3 (add_mem h1 h2)
    rw [← RingHom.map_add (f := _), ← RingHom.map_mul, ← add_mul, ← mul_assoc, ← hab, mul_add, a1, a2, add_zero] at h5
    exact (a4 _ hn).1 hi h5
  · rw [a3, b3, ← RingHom.map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε hε' hv, RingHom.map_zero]

theorem sum_orth {R ι : Type} [CommRing R] (c : R →+* R) (p q : ι → R) (s t : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ t, (p i + c (p i)) * (q j + c (q j)) = 0) :
    (∑ i ∈ s, p i + c (∑ i ∈ s, p i)) * (∑ j ∈ t, q j + c (∑ j ∈ t, q j)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h i hi j hj

theorem idemSum_orth : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  rintro D e e' P P' n ⟨⟨es, hes, rfl⟩, -⟩ ⟨⟨fs, hfs, rfl⟩, -⟩ hP hP'
  exact sum_orth (R := AE D) (cA D) es fs P P' fun i hi j hj =>
    idemAt_orth (hes i hi) (hfs j hj) (hP i hi) (hP' j hj)

end GlobalTheory.IdemOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def iotaW (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.InertLocField.liftT (E := E) v).toAddMonoidHom.comp
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom.toAddMonoidHom

def conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+* w.adicCompletion E :=
  (toCompl (under_eq_of_isInertAt hw)).comp
    ((sigR (Fv F v) σ).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom)

def glueW (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + P.map (iotaW hw)

def InLat {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (u : Fin d → K) : Prop :=
  ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u) i ∈ O

def InLat2 {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (z : Fin d ⊕ Fin d → K) : Prop :=
  InLat O b (z ∘ Sum.inl) ∧ InLat O b (z ∘ Sum.inr)

end GlobalTheory.InertBigCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_local_field_data_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
      (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧ (Valued.v δ = 1 ∧ σL δ = -δ) ∧
      (∀ x ∈ Formalism.UG.intL L, σL x = x → ψL x = 1) ∧ (∃ x ∈ Formalism.UG.intL L, σL x = x ∧ ψL (ϖ⁻¹ * x) ≠ 1) ∧
      Function.Injective ι ∧ (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) ∧
      (∀ x y, ι (x * y) = ι x * ι y) ∧ (∀ x, ι (σL x) = cA σ (ι x)) ∧
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) ∧
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) := by
  first | exact @GlobalTheory.InertLocField.field_data | exact GlobalTheory.InertLocField.field_data | (intros; apply GlobalTheory.InertLocField.field_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.SqTower

theorem integrableOn_ker'_of_stage_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  intro D T Lc sc G W i j p A A' WW X hX t P' h
  obtain ⟨-, -, -, -, -, hA', -, hIs⟩ := hX
  have hom : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hIs.weil' t
  have hpos : ∀ τ, (gramAt D A' τ).PosDef := fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (hA' τ)
  have hf : IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P') :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hIs.isVac'.1 hIs.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hIs.isVac'.1 hIs.isVac'.2.inf (hIs.snd t) hIs.isVac'.2.theta) P'
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D W.ψ hom.std A' WW _ _ (X.ω' t) hom hpos ℂ
    (LinearMap.toSpanSingleton ℂ _ (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P'))
    (fun x => GlobalTheory.OrientedHeis.theta_smul x hf) (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    X.m' X.fd' hIs.meas'.1 hIs.meas'.2 h
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at key
  exact key

end GlobalTheory.SqTower

end
end

